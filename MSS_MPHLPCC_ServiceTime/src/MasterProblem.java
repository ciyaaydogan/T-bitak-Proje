import ilog.concert.IloException;
import ilog.concert.IloIntVar;
import ilog.concert.IloLinearNumExpr;
import ilog.concert.IloNumVar;
import ilog.cplex.IloCplex;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.util.ArrayList;
import javax.sound.midi.Soundbank;

public class MasterProblem {

  IloCplex master;
  IloNumVar[][][][] z;
  IloIntVar[][][] y;
  IloNumVar[][][] a;
  IloNumVar[][][] b;
  IloNumVar[][][][] yy;
  IloNumVar[][] ohm;
  Data data;
  String dataFilePath;
  String paramsFilePath;
  String resultsFilePath;
  double StartTime;
  long begTime;
  double elapsedtotaltime;
  double elapsedsubTime;
  double elapsedmasterTime;
  long[] allThreadIds;
  long[] starttimeThreads;
  long[] FinishTimeThreads;

  MasterProblem(Data data, String dataFilePath, String paramsFilePath, double StartTime,
      String resultsFilePath) throws IloException, IOException {
    this.data = data;
    this.dataFilePath = dataFilePath;
    this.paramsFilePath = paramsFilePath;
    this.StartTime = StartTime;
    this.resultsFilePath = resultsFilePath;
    paramsFilePath = data.paramfp;
    dataFilePath = data.datafp;
    master = new IloCplex();
    CreateMP();
    SubProblem[][] sp = new SubProblem[data.nPeriod + 1][data.maxnumsce];
    for (int t = 1; t <= data.nPeriod; t++) {
      for (int sc : data.I[t]) {
        sp[t][sc] = new SubProblem(data, z[t][sc], y[t][sc], master, ohm[t][sc], t, sc);
      }
    }
    begTime = System.currentTimeMillis();
    LazyConstraintCallback cb = new LazyConstraintCallback(data, sp, master, z, y, yy, ohm,
        begTime,resultsFilePath);
    master.setParam(IloCplex.Param.TimeLimit, data.Time_Limit);
    ThreadMXBean threadMXBean = ManagementFactory.getThreadMXBean();
    allThreadIds = threadMXBean.getAllThreadIds();
    starttimeThreads = new long[allThreadIds.length];
    FinishTimeThreads = new long[allThreadIds.length];
    for (int i = 0; i < allThreadIds.length; i++) {
      starttimeThreads[i] = threadMXBean.getThreadCpuTime(allThreadIds[i]);
    }
    master.use(cb);
    master.exportModel("master.lp");
    master.solve();
    elapsedtotaltime = 0;
    long et = 0;
    for (int i = 0; i < allThreadIds.length; i++) {
      FinishTimeThreads[i] = threadMXBean.getThreadCpuTime(allThreadIds[i]);
    }
    for (int i = 0; i < allThreadIds.length; i++) {
      et = (et + FinishTimeThreads[i] - starttimeThreads[i]);
    }
    elapsedtotaltime = (double) (et / 1e9);
    elapsedsubTime = (double) (cb.elapsedTime / 1e9);
    elapsedmasterTime = elapsedtotaltime - elapsedsubTime;

    String Solution = "\n";
    Solution = Solution + String.valueOf(java.time.LocalDate.now()) + "_";
    Solution = Solution + String.valueOf(java.time.LocalTime.now()).substring(0, 5);
    Solution = Solution + "," + dataFilePath;
    Solution = Solution + "," + paramsFilePath;
    if (data.CompleteNetwork) {
      Solution = Solution + "," + "Complete";
    } else {
      Solution = Solution + "," + "Incomplete";
    }
    Solution = Solution + "," + data.nNodes;
    Solution = Solution + "," + data.nHubs;
    Solution = Solution + "," + data.nPeriod;
    Solution = Solution + ", w_up:" + data.W_up + " w_down: " + data.W_down;
    Solution = Solution + "," + data.g[1];
    Solution = Solution + "," + data.b;
    Solution = Solution + "," + data.Collection_Coeff;
    Solution = Solution + "," + data.alpha;
    Solution = Solution + "," + data.Distribution_Coeff;
    Solution = Solution + "," + data.Weight_Coeff;
    Solution = Solution + "," + data.Time_Limit;
    Solution = Solution + "," + data.Path_Length_Limit;
    Solution = Solution + "," + data.Num_Cap_Levels;
    Solution = Solution + "," + data.T_up;
    Solution = Solution + "," + data.delta_z;
    Solution = Solution + "," + data.baseusagerate;
    double[][] congestioncost = new double[data.nPeriod + 1][data.maxnumsce];
    if (master.getStatus() != IloCplex.Status.Infeasible) {
      for (int t = 1; t <= data.nPeriod; t++) {
        for (int sc : data.I[t]) {
          ArrayList<Integer> openedhubs = new ArrayList<>();
          for (int h : data.candhubs) {
            if (master.getValue(y[t][sc][h]) == 1) {
              openedhubs.add(h);
            }
          }
          //Update rhs of SubProblem
          for (int h : data.candhubs) {
            double rhs = 0;
            for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
              sp[t][sc].CapacityFlow[h][caplev].setUB(data.K[h][caplev] * master.getValue(z[t][sc][h][caplev]));
            }
          }

          for (int k = 0; k < data.num_od; k++) {
            for (int h : data.candhubs) {
              sp[t][sc].OpenedhubDemand[k][h].setUB(master.getValue(y[t][sc][h]));
            }
          }

          for (int k = 0; k < data.num_od; k++) {
            if (sp[t][sc].a[k] == 1) {
              sp[t][sc].originfirsthub[k]
                  .setBounds(master.getValue(sp[t][sc].rhs.get(sp[t][sc].originfirsthub[k])),
                      master.getValue(sp[t][sc].rhs.get(sp[t][sc].originfirsthub[k])));
            }
            if (sp[t][sc].b[k] == 1) {
              sp[t][sc].destlasthub[k]
                  .setBounds(master.getValue(sp[t][sc].rhs.get(sp[t][sc].destlasthub[k])),
                      master.getValue(sp[t][sc].rhs.get(sp[t][sc].destlasthub[k])));
            }
          }

                    /*IloLinearNumExpr[][] socp2new = new IloLinearNumExpr[data.nNodes][data.Num_Cap_Levels+1];
                    IloLinearNumExpr[][] socp3new = new IloLinearNumExpr[data.nNodes][data.Num_Cap_Levels+1];
                    for (int h : data.candhubs) {
                        for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
                            socp2new[h][caplev] = sp[t][sc].sub.linearNumExpr();
                            socp3new[h][caplev] = sp[t][sc].sub.linearNumExpr();

                            socp2new[h][caplev].addTerm(data.K[h][caplev], sp[t][sc].tneg[h][caplev]);
                            socp2new[h][caplev].addTerm(-1, sp[t][sc].tneg[h][caplev]);
                            sp[t][sc].socp2range[h][caplev].setExpr(socp2new[h][caplev]);
                            sp[t][sc].socp2range[h]
                                    .setBounds(master.getValue(z[t][sc][h]), master.getValue(z[t][sc][h]));
                            socp3new[h].addTerm(master.getValue(z[t][sc][h]), sp[t][sc].r[h]);
                            socp3new[h].addTerm(-2, sp[t][sc].u[h]);
                            socp3new[h].addTerm(-1, sp[t][sc].tpos[h]);
                            sp[t][sc].socp3range[h].setExpr(socp3new[h]);
                            sp[t][sc].socp3range[h]
                                    .setBounds(-1 * master.getValue(z[t][sc][h]), -1 * master.getValue(z[t][sc][h]));
                        }
                    }*/
          sp[t][sc].sub.setOut(null);
          sp[t][sc].sub.solve();
          System.out.println(t + "," + sc + " -- obj: " + sp[t][sc].sub.getObjValue());
          for (int h : data.candhubs) {
            for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
              congestioncost[t][sc] =
                  congestioncost[t][sc] + data.pr[t][sc] * master.getValue(z[t][sc][h][caplev]) * data.b * sp[t][sc].sub.getValue(sp[t][sc].r[h][caplev]);
              //System.out.println();
            }
          }
        }
      }

      System.out.println("DONE!");
      double[][] PeriodCost = new double[data.nPeriod + 1][data.maxnumsce];
      double fixedcost = 0;
      double capcost = 0;
      double congcost = 0;
      double totalsub = 0;
      double totalcost = 0;
      for (int t = 1; t <= data.nPeriod; t++) {
        for (int sc : data.I[t]) {
          for (int h : data.candhubs) {
            for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
              if (master.getValue(z[t][sc][h][caplev]) > 0) {
                System.out.println(
                    "y(" + t + "," + sc + "," + h + "): " + master.getValue(y[t][sc][h]) + " --- cap level(" + caplev + "): " + data.K[h][caplev] +"    ---"
                        + "a(" + t + "," + sc + "," + h + "): " + master.getValue(a[t][sc][h])
                        + " ----  " + "b(" + t + "," + sc + "," + h + "): " + master
                        .getValue(b[t][sc][h]) + "   r(" + t + "," + sc + "," + caplev + "): " + sp[t][sc].sub.getValue(sp[t][sc].r[h][caplev]) +
                        "   u(" + t + "," + sc + "," + caplev + "): " + sp[t][sc].sub.getValue(sp[t][sc].u[h][caplev]));
              }
            }
            fixedcost = fixedcost + master.getValue(a[t][sc][h]) * data.F[t][h];
            for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
              capcost = capcost + data.K[h][caplev] * master.getValue(z[t][sc][h][caplev]) * data.g[t];
            }
            PeriodCost[t][sc] = PeriodCost[t][sc] + master.getValue(a[t][sc][h]) * data.F[t][h];
            for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
              PeriodCost[t][sc] = PeriodCost[t][sc] + data.K[h][caplev] * master.getValue(z[t][sc][h][caplev]) * data.g[t];
            }
          }
          congcost = congcost + congestioncost[t][sc];
          totalsub = totalsub + sp[t][sc].sub.getObjValue();
          PeriodCost[t][sc] = PeriodCost[t][sc] + sp[t][sc].sub.getObjValue();
        }
      }
      totalcost = fixedcost + capcost + totalsub;
      Solution = Solution + "," + totalcost;
      Solution = Solution + "," + fixedcost;
      Solution = Solution + "," + capcost;
      System.out.println("Total cost: " + totalcost);
      System.out.println("Fixed Cost: " + fixedcost);
      System.out.println("Cap Cost: " + capcost);
      System.out.println("Cong Cost: " + congcost);
      Solution = Solution + "," + congcost;
      System.out.println("Routing Cost: " + (totalsub - congcost));
      Solution = Solution + "," + (totalsub - congcost);
      for (int t = 1; t <= data.nPeriod; t++) {
        for (int sc : data.I[t]) {
          System.out.println(t + "," + sc + "-subobj: " + sp[t][sc].sub.getObjValue());
          System.out.println(t + "," + sc + " -ohm: " + master.getValue(ohm[t][sc]));
          if (Math.abs(sp[t][sc].sub.getObjValue() - master.getValue(ohm[t][sc])) > 0.5) {
            System.out.println("!!!!!");

            File f = new File(resultsFilePath + "unsolvedcase_"+ data.paramfp + "_" + data.datafp +".txt");
            /* create a new file if not exists */
            if (!f.exists()) {
              try (var fw = new FileWriter(f);
                  var bw = new BufferedWriter(fw)) {
                bw.write("  t:" +t + "  sc:" + sc + "  final  ohm-sub da sorun");
              } catch (IOException e) {
                e.printStackTrace();
              }
            }
            try (var fw = new FileWriter(f, true);
                var bw = new BufferedWriter(fw)) {
              bw.write("  t:" +t + "  sc:" + sc + "  final  ohm-sub da sorun");
            } catch (IOException e) {
              e.printStackTrace();
            }

          }
        }
      }

      Solution = Solution + "," + master.getMIPRelativeGap();
      System.out.println("gap: " + master.getMIPRelativeGap());
      double finishTime;
      finishTime = System.currentTimeMillis();

      Solution = Solution + "," + elapsedtotaltime;
      Solution = Solution + "," + elapsedsubTime;
      Solution = Solution + "," + elapsedmasterTime;
      Solution = Solution + "," + cb.iteration;

      for (int t = 1; t <= data.nPeriod; t++) {
        for (int sc : data.I[t]) {
          Solution = Solution + "," + PeriodCost[t][sc] + ",";
          for (int h : data.candhubs) {
            if (master.getValue(y[t][sc][h]) > 0.1) {
              Solution = Solution + " " + h;
            }
          }
          Solution = Solution + ",";
          for (int h : data.candhubs) {
            for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
              if (master.getValue(z[t][sc][h][caplev]) > 0.1) {
                Solution = Solution + " " + (data.K[h][caplev] * master.getValue(z[t][sc][h][caplev]));
              }
            }
          }
          Solution = Solution + ",";
          for (int h : data.candhubs) {
            if (master.getValue(y[t][sc][h]) > 0.1) {
              for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
                Solution = Solution + " " + sp[t][sc].sub.getValue(sp[t][sc].u[h][caplev]);
              }
            }
          }
        }
      }
      Solution = Solution + "," + cb.OptCutCounter + ",";
      Solution = Solution + cb.addedPathCounter + ",";
      Solution = Solution + cb.deletedPathCounter + ",";
      Solution = Solution + master.getNnodes();

      System.out.println("elapsedtotaltime: " + elapsedtotaltime);
      System.out.println("elapsedmasterTime: " + elapsedmasterTime);
      System.out.println("elapsedsubTime: " + elapsedsubTime);
      Boolean feasible = true;
      for (int t = 1; t <= data.nPeriod; t++) {
        for (int sc : data.I[t]) {
          File fpaths = new File(
              resultsFilePath + paramsFilePath + "--" + dataFilePath + "--period" + t + "_" + sc
                  + ".csv");
          try (var fwfpaths = new FileWriter(fpaths);
              var bwfpaths = new BufferedWriter(fwfpaths)) {
            bwfpaths.write("paths");
            for (String p : sp[t][sc].path_vars.keySet()) {
              if (sp[t][sc].sub.getValue(sp[t][sc].path_vars.get(p)) > 1e-4) {
                bwfpaths.write("\n" + p + "," + sp[t][sc].path_cost.get(p));
                if (sp[t][sc].InfeasiblePaths.contains(p) & data.CompleteNetwork == false) {
                  System.out.println("The problem is INFEASIBLE!!");
                  feasible = false;
                  System.out.println("path: " + p + "    -- cost: " + sp[t][sc].path_cost.get(p));
                }
              }
            }
          }
        }
      }
      if (feasible == false) {
        Solution = Solution + ", INFEASIBLE";
      }
    } else {
      System.out.println("Problem is infeasible!");
      Solution = Solution + "," + "NO SOLUTION";
    }

    //Solution = Solution + "," + data.p;
    String top = "Date,Instance,Parameters,Network,Num nodes,Num candidate hubs,Num Periods,Scenario,CAP_C,CONGEST_C,COLLECT_C,TRANSFER_C,DISTRIB_C,WEIGHT_C,TIME_LIM,PATHLENGTH_LIM,NUM_CAPLEVELS,T_up,delta_z,baseusagerate,";
    top = top
        + "Total cost,Fixed cost,Capacity cost,Congestion cost,Routing cost,Gap (%),TotalTime (s),TotalSubTime, Total MasterTime,NumIteration,";
    for (int t = 1; t <= data.nPeriod; t++) {
      for (int sc : data.I[t]) {
        top = top + "PeriodCost(" + t + "_" + sc + "),";
        top = top + "Open hubs(" + t + "_" + sc + "),";
        top = top + "Capacities(" + t + "_" + sc + "),";
        top = top + "Traffics(" + t + "_" + sc + "),";
      }
    }
    top = top + "Number Opt Cut,";
    top = top + "Number Added Paths,";
    top = top + "Number Deleted Paths,";
    top = top + "Number Nodes,";
    File f = new File(resultsFilePath + "results.csv");
    /* create a new file if not exists */
    if (!f.exists()) {
      try (var fw = new FileWriter(f);
          var bw = new BufferedWriter(fw)) {
        bw.write(top);
      }
    }
    try (var fw = new FileWriter(f, true);
        var bw = new BufferedWriter(fw)) {
      bw.write(Solution);
    }
    master.end();
  }


  void CreateMP() throws IloException {
    //define variables
    z = new IloIntVar[data.nPeriod + 1][data.maxnumsce][data.nNodes][data.Num_Cap_Levels + 1];
    for (int t = 1; t <= data.nPeriod; t++) {
      for (int sc : data.I[t]) {
        for (int h : data.candhubs) {
          for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
            z[t][sc][h][caplev] = master.intVar(0, 1, "z(" + t + "," + sc + "," + h + "," + caplev + ")");
          }
        }
      }
    }

    y = new IloIntVar[data.nPeriod + 1][data.maxnumsce][data.nNodes];
    for (int t = 0; t <= data.nPeriod; t++) {
      for (int sc : data.I[t]) {
        for (int h : data.candhubs) {
          y[t][sc][h] = master.intVar(0, 1, "y(" + t + "," + sc + "," + h + ")");
        }
      }
    }

    yy = new IloNumVar[data.nPeriod + 1][data.maxnumsce][data.nNodes][data.nNodes];
    for (int t = 1; t <= data.nPeriod; t++) {
      for (int sc : data.I[t]) {
        for (int h1 : data.candhubs) {
          for (int h2 : data.candhubs) {
            yy[t][sc][h1][h2] = master
                .numVar(0, 1, "yy(" + t + "," + sc + "," + h1 + "," + h2 + ")");
          }
        }
      }
    }
    ohm = new IloNumVar[data.nPeriod + 1][data.maxnumsce];
    for (int t = 1; t <= data.nPeriod; t++) {
      for (int sc : data.I[t]) {
        ohm[t][sc] = master.numVar(0, Double.MAX_VALUE, "ohm(" + t + "," + sc + ")");
      }
    }

    //IloIntVar[][][] d = new IloIntVar[data.nPeriod + 1][data.maxnumsce][data.nNodes];
    for (int t = 1; t <= data.nPeriod; t++) {
      for (int sc : data.I[t]) {
        for (int h : data.candhubs) {
          //d[t][sc][h] = master.intVar(0, data.Num_Cap_Levels, "d(" + t + "," + sc + "," + h + ")");
        }
      }
    }

    a = new IloNumVar[data.nPeriod + 1][data.maxnumsce][data.nNodes];
    for (int t = 1; t <= data.nPeriod; t++) {
      for (int sc : data.I[t]) {
        for (int h : data.candhubs) {
          a[t][sc][h] = master.numVar(0, 1, "a(" + t + "," + sc + "," + h + ")");
        }
      }
    }

    b = new IloNumVar[data.nPeriod + 1][data.maxnumsce][data.nNodes];
    for (int t = 1; t <= data.nPeriod; t++) {
      for (int sc : data.I[t]) {
        for (int h : data.candhubs) {
          b[t][sc][h] = master.numVar(0, 1, "b(" + t + "," + sc + "," + h + ")");
        }
      }
    }

    //define objective function
    IloLinearNumExpr masterObF = master.linearNumExpr();
    for (int t = 1; t <= data.nPeriod; t++) {
      for (int sc : data.I[t]) {
        for (int h : data.candhubs) {
          masterObF.addTerm(data.pr[t][sc] * data.F[t][h], a[t][sc][h]);
        }
      }
    }
    for (int t = 1; t <= data.nPeriod; t++) {
      for (int sc : data.I[t]) {
        for (int h : data.candhubs) {
          masterObF.addTerm(data.pr[t][sc] * data.B[t][h], b[t][sc][h]);
        }
      }
    }
    for (int t = 1; t <= data.nPeriod; t++) {
      for (int sc : data.I[t]) {
        for (int h : data.candhubs) {
          for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
            masterObF.addTerm(data.pr[t][sc] * data.g[t] * data.K[h][caplev], z[t][sc][h][caplev]);
          }

        }
      }
    }
    for (int t = 1; t <= data.nPeriod; t++) {
      for (int sc : data.I[t]) {
        masterObF.addTerm(1, ohm[t][sc]);
      }
    }

    master.addMinimize(masterObF);

    // sum_{l} Z(h,l) <= y(h) \forall h
    IloLinearNumExpr[][][] exprmasterconst1 = new IloLinearNumExpr[data.nPeriod
        + 1][data.maxnumsce][data.nNodes];
    for (int t = 1; t <= data.nPeriod; t++) {
      for (int sc : data.I[t]) {
        for (int h : data.candhubs) {
          exprmasterconst1[t][sc][h] = master.linearNumExpr();
          for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
            exprmasterconst1[t][sc][h].addTerm(1, z[t][sc][h][caplev]);
          }
          exprmasterconst1[t][sc][h].addTerm(-1, y[t][sc][h]);
          master.addLe(exprmasterconst1[t][sc][h], 0,
              "openedhubs_capacity(" + t + "," + sc + "," + h + ")");
        }
      }
    }

    // Total flow should satisfy total flows on all opened hubs
    IloLinearNumExpr[][] exprmasterconst2 = new IloLinearNumExpr[data.nPeriod + 1][data.maxnumsce];
    for (int t = 1; t <= data.nPeriod; t++) {
      for (int sc : data.I[t]) {
        exprmasterconst2[t][sc] = master.linearNumExpr();
        for (int h : data.candhubs) {
          for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
            exprmasterconst2[t][sc].addTerm(data.K[h][caplev], z[t][sc][h][caplev]);
          }
        }
        for (int h1 : data.candhubs) {
          for (int h2 : data.candhubs) {
            exprmasterconst2[t][sc]
                .addTerm(-1 * data.WW[t][sc][h1][h2] * data.CongCoef, yy[t][sc][h1][h2]);
          }
        }
        master.addGe(exprmasterconst2[t][sc], data.totalflow[t][sc] * data.CongCoef,
            "totalCap_totalflow(" + t + "," + sc + ")");
      }
    }

      /*  //For Discrete Z(h)
        for (int t = 1; t <= data.nPeriod; t++) {
            for (int sc : data.I[t]) {
                for (int h : data.candhubs) {
                    master.addLe(d[t][sc][h], data.Num_Cap_Levels,
                            "Variable d(" + t + "," + sc + "," + h + ")");
                }
            }
        }*/

        /*IloLinearNumExpr[][][] exprmasterconst3 = new IloLinearNumExpr[data.nPeriod
                + 1][data.maxnumsce][data.nNodes];
        for (int t = 1; t <= data.nPeriod; t++) {
            for (int sc : data.I[t]) {
                for (int h : data.candhubs) {
                    exprmasterconst3[t][sc][h] = master.linearNumExpr();
                    for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
                        exprmasterconst3[t][sc][h].addTerm(data.K[h][caplev], z[t][sc][h][caplev]);
                    }
                    exprmasterconst3[t][sc][h].addTerm((-1 * data.Q[h]) / data.Num_Cap_Levels, d[t][sc][h]);
                    master.addEq(exprmasterconst3[t][sc][h], 0,
                            "DiscreteCapacity(" + t + "," + sc + "," + h + ")");
                }
            }
        }*/

    //For yy(h1,h2) variables
    IloLinearNumExpr[][][][] feasconst1 = new IloLinearNumExpr[data.nPeriod
        + 1][data.maxnumsce][data.nNodes][data.nNodes];
    for (int t = 1; t <= data.nPeriod; t++) {
      for (int sc : data.I[t]) {
        for (int h1 : data.candhubs) {
          for (int h2 : data.candhubs) {
            feasconst1[t][sc][h1][h2] = master.linearNumExpr();
            feasconst1[t][sc][h1][h2].addTerm(1, y[t][sc][h1]);
            feasconst1[t][sc][h1][h2].addTerm(1, y[t][sc][h2]);
            feasconst1[t][sc][h1][h2].addTerm(-1, yy[t][sc][h1][h2]);
            master.addLe(feasconst1[t][sc][h1][h2], 1,
                "feasiblityconst1(" + t + "," + sc + "," + h1 + "," + h2 + ")");
          }
        }
      }
    }
    IloLinearNumExpr[][][][] feasconst2 = new IloLinearNumExpr[data.nPeriod
        + 1][data.maxnumsce][data.nNodes][data.nNodes];
    for (int t = 1; t <= data.nPeriod; t++) {
      for (int sc : data.I[t]) {
        for (int h1 : data.candhubs) {
          for (int h2 : data.candhubs) {
            feasconst2[t][sc][h1][h2] = master.linearNumExpr();
            feasconst2[t][sc][h1][h2].addTerm(1, y[t][sc][h1]);
            feasconst2[t][sc][h1][h2].addTerm(-1, y[t][sc][h2]);
            feasconst2[t][sc][h1][h2].addTerm(1, yy[t][sc][h1][h2]);
            master.addLe(feasconst2[t][sc][h1][h2], 1,
                "feasiblityconst2(" + t + "," + sc + "," + h1 + "," + h2 + ")");
          }
        }
      }
    }
    IloLinearNumExpr[][][][] feasconst3 = new IloLinearNumExpr[data.nPeriod
        + 1][data.maxnumsce][data.nNodes][data.nNodes];
    for (int t = 1; t <= data.nPeriod; t++) {
      for (int sc : data.I[t]) {
        for (int h1 : data.candhubs) {
          for (int h2 : data.candhubs) {
            feasconst3[t][sc][h1][h2] = master.linearNumExpr();
            feasconst3[t][sc][h1][h2].addTerm(-1, y[t][sc][h1]);
            feasconst3[t][sc][h1][h2].addTerm(1, y[t][sc][h2]);
            feasconst3[t][sc][h1][h2].addTerm(1, yy[t][sc][h1][h2]);
            master.addLe(feasconst3[t][sc][h1][h2], 1,
                "feasiblityconst3(" + t + "," + sc + "," + h1 + "," + h2 + ")");
          }
        }
      }
    }
    IloLinearNumExpr[][][][] feasconst4 = new IloLinearNumExpr[data.nPeriod
        + 1][data.maxnumsce][data.nNodes][data.nNodes];
    for (int t = 1; t <= data.nPeriod; t++) {
      for (int sc : data.I[t]) {
        for (int h1 : data.candhubs) {
          for (int h2 : data.candhubs) {
            feasconst4[t][sc][h1][h2] = master.linearNumExpr();
            feasconst4[t][sc][h1][h2].addTerm(1, y[t][sc][h1]);
            feasconst4[t][sc][h1][h2].addTerm(1, y[t][sc][h2]);
            feasconst4[t][sc][h1][h2].addTerm(-1, yy[t][sc][h1][h2]);
            master.addGe(feasconst4[t][sc][h1][h2], 0,
                "feasiblityconst4(" + t + "," + sc + "," + h1 + "," + h2 + ")");
          }
        }
      }
    }

    //Each opened hub should have capacity at least its out and in flow
    IloLinearNumExpr[][][] exprmasterconst4 = new IloLinearNumExpr[data.nPeriod
        + 1][data.maxnumsce][data.nNodes];
    for (int t = 1; t <= data.nPeriod; t++) {
      for (int sc : data.I[t]) {
        for (int h : data.candhubs) {
          exprmasterconst4[t][sc][h] = master.linearNumExpr();
          for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
            exprmasterconst4[t][sc][h].addTerm(data.K[h][caplev], z[t][sc][h][caplev]);
          }
          exprmasterconst4[t][sc][h]
              .addTerm(-1 * data.HminCap[t][sc][h] * data.CongCoef, y[t][sc][h]);
          master
              .addGe(exprmasterconst4[t][sc][h], 0, "min_cap_for(" + t + "," + sc + "," + h + ")");
        }
      }
    }

    for (int h : data.candhubs) {
      master.addEq(y[0][1][h], 0);
    }

    IloLinearNumExpr[][][] const6 = new IloLinearNumExpr[data.nPeriod
        + 1][data.maxnumsce][data.nNodes];
    for (int t = 1; t <= data.nPeriod; t++) {
      for (int sc : data.I[t]) {
        for (int h : data.candhubs) {
          const6[t][sc][h] = master.linearNumExpr();
          const6[t][sc][h].addTerm(1, y[t][sc][h]);
          const6[t][sc][h].addTerm(-1, y[t - 1][data.a[sc]][h]);
          const6[t][sc][h].addTerm(-1, a[t][sc][h]);
          master
              .addLe(const6[t][sc][h], 0, "multiperiodconstraint1(" + t + "," + sc + "," + h + ")");
        }
      }
    }
    IloLinearNumExpr[][][] const7 = new IloLinearNumExpr[data.nPeriod
        + 1][data.maxnumsce][data.nNodes];
    for (int t = 1; t <= data.nPeriod; t++) {
      for (int sc : data.I[t]) {
        for (int h : data.candhubs) {
          const7[t][sc][h] = master.linearNumExpr();
          const7[t][sc][h].addTerm(1, y[t][sc][h]);
          const7[t][sc][h].addTerm(-1, a[t][sc][h]);
          master
              .addGe(const7[t][sc][h], 0, "multiperiodconstraint2(" + t + "," + sc + "," + h + ")");
        }
      }
    }
    IloLinearNumExpr[][][] const8 = new IloLinearNumExpr[data.nPeriod
        + 1][data.maxnumsce][data.nNodes];
    for (int t = 1; t <= data.nPeriod; t++) {
      for (int sc : data.I[t]) {
        for (int h : data.candhubs) {
          const8[t][sc][h] = master.linearNumExpr();
          const8[t][sc][h].addTerm(1, y[t][sc][h]);
          const8[t][sc][h].addTerm(1, y[t - 1][data.a[sc]][h]);
          const8[t][sc][h].addTerm(1, a[t][sc][h]);
          master
              .addLe(const8[t][sc][h], 2, "multiperiodconstraint3(" + t + "," + sc + "," + h + ")");
        }
      }
    }
    IloLinearNumExpr[][][] const9 = new IloLinearNumExpr[data.nPeriod
        + 1][data.maxnumsce][data.nNodes];
    for (int t = 1; t <= data.nPeriod; t++) {
      for (int sc : data.I[t]) {
        for (int h : data.candhubs) {
          const9[t][sc][h] = master.linearNumExpr();
          const9[t][sc][h].addTerm(1, y[t - 1][data.a[sc]][h]);
          const9[t][sc][h].addTerm(-1, y[t][sc][h]);
          const9[t][sc][h].addTerm(-1, b[t][sc][h]);
          master
              .addLe(const9[t][sc][h], 0, "multiperiodconstraint4(" + t + "," + sc + "," + h + ")");
        }
      }
    }
    IloLinearNumExpr[][][] const10 = new IloLinearNumExpr[data.nPeriod
        + 1][data.maxnumsce][data.nNodes];
    for (int t = 1; t <= data.nPeriod; t++) {
      for (int sc : data.I[t]) {
        for (int h : data.candhubs) {
          const10[t][sc][h] = master.linearNumExpr();
          const10[t][sc][h].addTerm(1, y[t - 1][data.a[sc]][h]);
          const10[t][sc][h].addTerm(-1, b[t][sc][h]);
          master.addGe(const10[t][sc][h], 0,
              "multiperiodconstraint5(" + t + "," + sc + "," + h + ")");
        }
      }
    }
    IloLinearNumExpr[][][] const11 = new IloLinearNumExpr[data.nPeriod
        + 1][data.maxnumsce][data.nNodes];
    for (int t = 1; t <= data.nPeriod; t++) {
      for (int sc : data.I[t]) {
        for (int h : data.candhubs) {
          const11[t][sc][h] = master.linearNumExpr();
          const11[t][sc][h].addTerm(1, y[t][sc][h]);
          const11[t][sc][h].addTerm(1, y[t - 1][data.a[sc]][h]);
          const11[t][sc][h].addTerm(1, b[t][sc][h]);
          master.addLe(const11[t][sc][h], 2,
              "multiperiodconstraint6(" + t + "," + sc + "," + h + ")");
        }
      }
    }

        /*IloLinearNumExpr[][] const_p = new IloLinearNumExpr[data.nPeriod + 1][data.maxnumsce];
        for (int t = 1; t <= data.nPeriod; t++) {
            for (int sc : data.I[t]) {
                const_p[t][sc] = master.linearNumExpr();
                for (int h : data.candhubs) {
                    const_p[t][sc].addTerm(1, y[t][sc][h]);
                }
                //master.addEq(const_p[t][sc], data.p, "const_p(" + t + "," + sc + ")");
            }
        }*/

    //valid constraints
    if (data.CompleteNetwork) {
      IloLinearNumExpr[][] validineq = new IloLinearNumExpr[data.nPeriod + 1][data.maxnumsce];
      for (int t = 1; t <= data.nPeriod; t++) {
        for (int sc : data.I[t]) {
          validineq[t][sc] = master.linearNumExpr();
          for (int h : data.candhubs) {
            validineq[t][sc].addTerm(1, y[t][sc][h]);
          }
          master.addGe(validineq[t][sc], data.sigma[t][sc], "valid ineq(" + t + "," + sc + ")");
        }
      }
    } else {
      IloLinearNumExpr[][][] validineq = new IloLinearNumExpr[data.nPeriod
          + 1][data.maxnumsce][data.nNodes];
      for (int t = 1; t <= data.nPeriod; t++) {
        for (int sc : data.I[t]) {
          for (int i = 0; i < data.nNodes; i++) {
            validineq[t][sc][i] = master.linearNumExpr();
            for (int h : data.candhubs) {
              if (data.C[t][i][h] != data.bigM) {
                validineq[t][sc][i].addTerm(1, y[t][sc][h]);
              }
            }
            master.addGe(validineq[t][sc][i], data.sigma_n[t][sc][i],
                "valid ineq(" + t + "," + sc + "," + i + ")");
          }
        }
      }
    }

  }
}
