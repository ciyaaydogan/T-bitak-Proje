import ilog.concert.IloException;
import ilog.concert.IloIntVar;
import ilog.concert.IloNumExpr;
import ilog.concert.IloNumVar;
import ilog.concert.IloRange;
import ilog.cplex.IloCplex;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.util.ArrayList;


public class LazyConstraintCallback extends IloCplex.LazyConstraintCallback {

  Data data;
  SubProblem[][] sp;
  IloCplex master;
  IloNumVar[][][][] z;
  IloIntVar[][][] y;
  IloNumVar[][][][] yy;
  IloNumVar[][] ohm;
  long begTime;
  //ArrayList<Integer> OpenedHubs;
  //HashMap<String, Double> path_cost;
  int iteration = 0;
  double[][] dual_demandSatisy;
  double[][] dual_Flow;
  double[][][] dual_CapacityFlow;
  double[][][] dual_OpenedhubDemand;
  double[][] dual_originfirsthub;
  double[][] dual_destlasthub;
  double[][][] dual_socp2;
  double[][][] dual_socp3;
  String addedpaths = "";

  long[] allThreadIds;
  long[] starttimeThreads;
  long[] FinishTimeThreads;
  long elapsedTime = 0;
  String resultsFilePath;
  int OptCutCounter = 0;
  int addedPathCounter = 0;
  int deletedPathCounter = 0;


  LazyConstraintCallback(Data data, SubProblem[][] sp, IloCplex master, IloNumVar[][][][] z,
      IloIntVar[][][] y, IloNumVar[][][][] yy, IloNumVar[][] ohm, long begTime,
      String resultsFilePath) {
    this.data = data;
    this.sp = sp;
    this.master = master;
    this.z = z;
    this.y = y;
    this.yy = yy;
    this.ohm = ohm;
    this.begTime = begTime;
    this.resultsFilePath = resultsFilePath;
  }


  @Override
  protected void main() throws IloException {
    ThreadMXBean threadMXBean = ManagementFactory.getThreadMXBean();
    allThreadIds = threadMXBean.getAllThreadIds();
    starttimeThreads = new long[allThreadIds.length];
    FinishTimeThreads = new long[allThreadIds.length];
    for (int i = 0; i < allThreadIds.length; i++) {
      starttimeThreads[i] = threadMXBean.getThreadCpuTime(allThreadIds[i]);
    }

    iteration = iteration + 1;
    if (data.print) {
      System.out.println("----------------------------");
      System.out.println("Iteration: " + iteration);
      System.out.println("Master Objective: " + getObjValue());
    }
    for (int t = 1; t <= data.nPeriod; t++) {
      for (int sc : data.I[t]) {

        if (data.print) {
          System.out.println("ohm(" + t + "," + sc + ") :" + getValue(ohm[t][sc]));
        }
        ArrayList<Integer> openedhubs = new ArrayList<>();
        for (int h : data.candhubs) {
          if (data.print) {
            System.out.println(
                "y(" + t + "," + sc + "," + h + "): " + getValue(y[t][sc][h]));
          }
          if (getValue(y[t][sc][h]) == 1) {
            openedhubs.add(h);
          }
        }

        //Update times
        for (int k = 0; k < data.num_od; k++) {
          int ori = data.k_od.get(k)[0];
          int des = data.k_od.get(k)[1];
          Label L = new Label();
          L.n = ori;
          L.c = 0;
          L.l = data.Path_Length_Limit;
          L.N = new ArrayList<>(openedhubs);
          L.hubs = new ArrayList();
          L.path = "p#" + ori;
          if (data.candhubs.contains(ori)) {
            L.path = L.path + "_" + ori;
            L.hubs.add(ori);
          }
          ArrayList<Label>[] Labels = new ArrayList[data.nNodes];
          for (int n : L.N) {
            Labels[n] = new ArrayList<>();
            Label L_ = new Label();
            L_.n = n;
            L_.c = L.c + data.time[1][ori][n];
            L_.N = new ArrayList<>(L.N);
            L_.N.remove(Integer.valueOf(n));
            L_.hubs = new ArrayList<>(L.hubs);
            L_.hubs.add(n);
            L_.path = L.path;
            L_.path = L_.path + "_" + n;
            L_.l = L.l - 1;
            Labels[n].add(L_);
          }
          L.processed = true;
          boolean devam = true;
          ArrayList<Label>[] NewAdddedLabels = new ArrayList[data.nNodes];
          for (int n : L.N) {
            NewAdddedLabels[n] = new ArrayList<>();
          }
          while (devam) {
            devam = false;
            for (int n : L.N) {
              for (Label lab : Labels[n]) {
                if (lab.l - 1 >= 1 & lab.processed == false & lab.N.size() > 0) {
                  for (int n_ : lab.N) {
                    Label L_ = new Label();
                    L_.c = lab.c + data.time[1][lab.n][n_];
                    L_.n = n_;
                    L_.N = new ArrayList<>(lab.N);
                    L_.N.remove(Integer.valueOf(n_));
                    L_.hubs = new ArrayList<>(lab.hubs);
                    L_.hubs.add(n_);
                    L_.path = lab.path + "_" + n_;
                    L_.l = lab.l - 1;
                    NewAdddedLabels[n_].add(L_);
                  }
                  lab.processed = true;
                  devam = true;
                }
              }
            }
            //elimination
            for (int n : L.N) {
              for (Label lab1 : Labels[n]) {
                for (Label lab2 : NewAdddedLabels[n]) {
                  if (lab1.c < lab2.c) {
                    lab2.processed = true;
                  }
                }
              }
            }
            //add new labels
            for (int n : L.N) {
              for (Label lab : NewAdddedLabels[n]) {
                Labels[n].add(lab);
              }
            }
            //reset
            for (int n : L.N) {
              NewAdddedLabels[n] = new ArrayList<>();
            }
          }
          double T_min = Double.MAX_VALUE;
          for (int n : L.N) {
            for (Label lab : Labels[n]) {
              lab.c = lab.c + data.time[1][lab.n][des];
              lab.path = lab.path + "_" + des;
              if (openedhubs.contains(des)) {
                lab.path = lab.path + "_" + des;
                lab.hubs.add(des);
              }
              if (T_min > lab.c) {
                T_min = lab.c;
              }
            }
          }
          data.Tmin[1][k] = T_min * data.T_up;
          for (int tt = 1; tt < data.nPeriod; tt++) {
            data.Tmin[tt + 1][k] = data.Tmin[tt][k] * (1 + data.T_a);
          }
          for (int tt = 1; tt <= data.nPeriod; tt++) {
            data.Tmin[tt][k] = data.Tmin[tt][k] + data.expHubTime;
          }
        }

        //update ObjFunc
                /*for (int h : data.candhubs) {
                    for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
                        sp[t][sc].sub.setLinearCoef(sp[t][sc].SubObjFunc, data.pr[t][sc] * data.b * getValue(z[t][sc][h][caplev]), sp[t][sc].r[h][caplev]);
                    }
                }*/
        //Update rhs of SubProblem
        for (int h : data.candhubs) {
          double CapacityFlowrhs = 0;
          for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
            if (data.K[h][caplev] * getValue(z[t][sc][h][caplev]) < 0) {
              sp[t][sc].CapacityFlow[h][caplev]
                  .setUB(0);
            } else {
              sp[t][sc].CapacityFlow[h][caplev]
                  .setUB(data.K[h][caplev] * getValue(z[t][sc][h][caplev]));
            }
          }

        }

        for (int k = 0; k < data.num_od; k++) {
          for (int h : data.candhubs) {
            sp[t][sc].OpenedhubDemand[k][h].setUB(getValue(y[t][sc][h]));
          }
        }

        for (int k = 0; k < data.num_od; k++) {
          if (sp[t][sc].a[k] == 1) {
                        /*if (getValue(sp[t][sc].rhs.get(sp[t][sc].originfirsthub[k])) > 0.5 ){
                            sp[t][sc].originfirsthub[k]
                                    .setLB(getValue(sp[t][sc].rhs.get(sp[t][sc].originfirsthub[k])));
                            sp[t][sc].originfirsthub[k]
                                    .setUB(Double.MAX_VALUE);
                        }else {
                            sp[t][sc].originfirsthub[k]
                                    .setUB(getValue(sp[t][sc].rhs.get(sp[t][sc].originfirsthub[k])));
                            sp[t][sc].originfirsthub[k]
                                    .setLB(-Double.MAX_VALUE);
                        }*/
            sp[t][sc].originfirsthub[k]
                .setBounds(getValue(sp[t][sc].rhs.get(sp[t][sc].originfirsthub[k])),
                    getValue(sp[t][sc].rhs.get(sp[t][sc].originfirsthub[k])));
          }
          if (sp[t][sc].b[k] == 1) {
                        /*if (getValue(sp[t][sc].rhs.get(sp[t][sc].destlasthub[k])) > 0.5){
                            sp[t][sc].destlasthub[k].setLB(getValue(sp[t][sc].rhs.get(sp[t][sc].destlasthub[k])));
                            sp[t][sc].destlasthub[k].setUB(Double.MAX_VALUE);
                        }else {
                            sp[t][sc].destlasthub[k].setUB(getValue(sp[t][sc].rhs.get(sp[t][sc].destlasthub[k])));
                            sp[t][sc].destlasthub[k].setLB(-Double.MAX_VALUE);
                        }*/
            sp[t][sc].destlasthub[k]
                .setBounds(getValue(sp[t][sc].rhs.get(sp[t][sc].destlasthub[k])),
                    getValue(sp[t][sc].rhs.get(sp[t][sc].destlasthub[k])));
          }
        }

                /*IloLinearNumExpr[][] socp2new = new IloLinearNumExpr[data.nPeriod + 1][data.nNodes];
                IloLinearNumExpr[][] socp3new = new IloLinearNumExpr[data.nPeriod + 1][data.nNodes];
                for (int h : data.candhubs) {
                    socp2new[t][h] = sp[t][sc].sub.linearNumExpr();
                    socp3new[t][h] = sp[t][sc].sub.linearNumExpr();

                    socp2new[t][h].addTerm(getValue(z[t][sc][h]), sp[t][sc].r[h]);
                    socp2new[t][h].addTerm(-1, sp[t][sc].tneg[h]);
                    sp[t][sc].socp2range[h].setExpr(socp2new[t][h]);
                    sp[t][sc].socp2range[h].setBounds(getValue(z[t][sc][h]), getValue(z[t][sc][h]));
                    //System.out.println("new socp2: "+sp[t].socp2range[h].getExpr());

                    socp3new[t][h].addTerm(getValue(z[t][sc][h]), sp[t][sc].r[h]);
                    socp3new[t][h].addTerm(-2, sp[t][sc].u[h]);
                    socp3new[t][h].addTerm(-1, sp[t][sc].tpos[h]);
                    sp[t][sc].socp3range[h].setExpr(socp3new[t][h]);
                    sp[t][sc].socp3range[h].setBounds(-1 * getValue(z[t][sc][h]), -1 * getValue(z[t][sc][h]));
                    //System.out.println("new socp3: "+sp[t].socp3range[h].getExpr());
                }*/

        //sp[t][sc].sub.exportModel("it" + iteration + "_sub(" + t + "_" + sc + ").lp");
        //sp[t][sc].sub.setParam(IloCplex.Param.Preprocessing.Reduce, 0);
        sp[t][sc].sub.setOut(null);
        //sp[t][sc].sub.solve();
        //sp[t][sc].sub.setParam(IloCplex.Param.Barrier.Algorithm, 3);
        boolean cont_sub_failed = true;
        if (!sp[t][sc].sub.solve()) {
          cont_sub_failed = false;
          System.out.println(iteration + " - " + t + " - " + sc);
          for (int h : data.candhubs) {
            for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
              System.out.println(
                  "t: " + t + " sc:" + sc + " h: " + h + " caplevel: " + caplev + "    " + getValue(
                      z[t][sc][h][caplev]));
            }
          }
          sp[t][sc].sub.exportModel("infeasiblesub.lp");
          for (int h : data.candhubs) {
            double tot_u = 0;
            for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
              System.out.println(
                  "u(" + h + "," + caplev + "): " + sp[t][sc].sub.getValue(sp[t][sc].u[h][caplev]));
              tot_u = tot_u + sp[t][sc].sub.getValue(sp[t][sc].u[h][caplev]);
              System.out.println("z(" + h + "," + caplev + "): " + getValue(z[t][sc][h][caplev]));
              //System.out.println(sp[t][sc].sub.getValue(sp[t][sc].u[h]) / (getValue(z[t][sc][h][caplev]) - sp[t][sc].sub.getValue(sp[t][sc].u[h])));
            }
            System.out.println("u(" + h + "): " + tot_u);
          }
          double aa = 0;
          for (int k = 0; k < data.num_od; k++) {
            System.out.println("k:" + k + "   W_k:" + data.W[t][sc][k]);
            for (String p : sp[t][sc].k_paths.get(k)) {
              System.out.println("k: " + k + "  " + p + ":  " + sp[t][sc].sub
                  .getValue(sp[t][sc].path_vars.get(p)));
              aa = aa + data.W[t][sc][k] * sp[t][sc].sub.getValue(sp[t][sc].path_vars.get(p));
            }
          }
          System.out.println("aa: " + aa);
          System.out.println("obj: " + sp[t][sc].sub.getObjValue());
          System.out.println(" ");
          File f = new File(
              resultsFilePath + "unsolvedcase_" + data.paramfp + "_" + data.datafp + ".txt");
          /* create a new file if not exists */
          if (!f.exists()) {
            try (var fw = new FileWriter(f);
                var bw = new BufferedWriter(fw)) {
              bw.write("iteration: " + iteration + "  t:" + t + "  sc:" + sc);
            } catch (IOException e) {
              e.printStackTrace();
            }
          }
          try (var fw = new FileWriter(f, true);
              var bw = new BufferedWriter(fw)) {
            bw.write("iteration: " + iteration + "  t:" + t + "  sc:" + sc);
          } catch (IOException e) {
            e.printStackTrace();
          }
        }

        if (data.print) {
          System.out
              .println("Sub Objective(" + t + "," + sc + "): " + sp[t][sc].sub.getObjValue());
        }

        for (int h : data.candhubs) {
          if (data.print) {
            for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
              System.out.println("z(" + h + "," + caplev + "): " + getValue(z[t][sc][h][caplev]));
              System.out.println(
                  "u(" + h + "," + caplev + "): " + sp[t][sc].sub.getValue(sp[t][sc].u[h][caplev]));
            }
          }
        }

        for (int h : data.candhubs) {
          if (data.print) {
            for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
              System.out.println(
                  "r(" + h + "," + caplev + "): " + sp[t][sc].sub.getValue(sp[t][sc].r[h][caplev]));
            }
          }
        }

        if (getValue(ohm[t][sc]) / sp[t][sc].sub.getObjValue() < 0.9999) {
          boolean cg = true;
          int loop = 0;
          while (cg) {
            loop = loop + 1;
            cg = false;

            double[][] r_value = new double[data.nNodes][data.Num_Cap_Levels + 1];
            for (int h : data.candhubs) {
              for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
                r_value[h][caplev] = sp[t][sc].sub.getValue(sp[t][sc].r[h][caplev]);
              }
            }

            //getDuals
            dual_demandSatisy = new double[data.nPeriod + 1][data.num_od];
            for (int k = 0; k < data.num_od; k++) {
              dual_demandSatisy[t][k] = sp[t][sc].sub.getDual(sp[t][sc].demandSatisy[k]);
            }

            dual_Flow = new double[data.nPeriod + 1][data.nNodes];
            for (int h : data.candhubs) {
              dual_Flow[t][h] = sp[t][sc].sub.getDual(sp[t][sc].Flow[h]);
            }

            dual_CapacityFlow = new double[data.nPeriod + 1][data.nNodes][data.Num_Cap_Levels + 1];
            for (int h : data.candhubs) {
              for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
                dual_CapacityFlow[t][h][caplev] = sp[t][sc].sub
                    .getDual(sp[t][sc].CapacityFlow[h][caplev]);
              }
            }

            dual_OpenedhubDemand = new double[data.nPeriod + 1][data.num_od][data.nNodes];
            for (int k = 0; k < data.num_od; k++) {
              for (int h : data.candhubs) {
                dual_OpenedhubDemand[t][k][h] = sp[t][sc].sub
                    .getDual(sp[t][sc].OpenedhubDemand[k][h]);
              }
            }

            dual_originfirsthub = new double[data.nPeriod + 1][data.num_od];
            for (int k = 0; k < data.num_od; k++) {
              if (sp[t][sc].a[k] == 1) {
                dual_originfirsthub[t][k] = sp[t][sc].sub.getDual(sp[t][sc].originfirsthub[k]);
              }
            }

            dual_destlasthub = new double[data.nPeriod + 1][data.num_od];
            for (int k = 0; k < data.num_od; k++) {
              if (sp[t][sc].b[k] == 1) {
                dual_destlasthub[t][k] = sp[t][sc].sub.getDual(sp[t][sc].destlasthub[k]);
              }
            }

            dual_socp2 = new double[data.nPeriod + 1][data.nNodes + 1][data.Num_Cap_Levels + 1];
            for (int h : data.candhubs) {
              for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
                dual_socp2[t][h][caplev] = sp[t][sc].sub.getDual(sp[t][sc].socp2range[h][caplev]);
              }
            }
            dual_socp3 = new double[data.nPeriod + 1][data.nNodes + 1][data.Num_Cap_Levels + 1];
            for (int h : data.candhubs) {
              for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
                dual_socp3[t][h][caplev] = sp[t][sc].sub.getDual(sp[t][sc].socp3range[h][caplev]);
              }
            }

            if (data.cpx_true_labeling_false) {
                        /*for (int k = 0; k < data.num_od; k++) {
                            double[][] cnn = new double[data.nNodes][data.nNodes + 1];
                            int ori = data.k_od.get(k)[0];
                            int des = data.k_od.get(k)[1];
                            int m = 0;
                            if (openedhubs.contains(ori)) {
                                m = m + 1;
                            }
                            if (openedhubs.contains(des)) {
                                m = m + 1;
                            }
                            if (openedhubs.contains(ori)) {
                                cnn[ori][ori] = data.W[t][k] * data.C[t][ori][ori] * data.Collection_Coeff - dual_demandSatisy[t][k] - data.W[t][k] * dual_Flow[t][ori] - dual_OpenedhubDemand[t][k][ori] - dual_originfirsthub[t][k];
                            } else {
                                for (int n : openedhubs) {
                                    cnn[ori][n] = data.W[t][k] * data.C[t][ori][n] * data.Collection_Coeff - dual_demandSatisy[t][k] - data.W[t][k] * dual_Flow[t][n] - dual_OpenedhubDemand[t][k][n];
                                }
                            }

                            if (openedhubs.contains(des)) {
                                cnn[des][des] = data.W[t][k] * data.C[t][des][des] * data.Distribution_Coeff - dual_destlasthub[t][k];
                            } else {
                                for (int n_ : openedhubs) {
                                    cnn[n_][des] = data.W[t][k] * data.C[t][n_][des] * data.Distribution_Coeff;
                                }
                            }

                            for (int n : openedhubs) {
                                for (int n_ : openedhubs) {
                                    if (n != n_) {
                                        cnn[n][n_] = data.W[t][k] * data.C[t][n][n_] * data.alpha - data.W[t][k] * dual_Flow[t][n_] - dual_OpenedhubDemand[t][k][n_];
                                    }
                                }
                            }
                            IloCplex cpx = new IloCplex();
                            cpx.setOut(null);
                            IloIntVar[][] x = new IloIntVar[data.nNodes][data.nNodes];
                            IloNumVar[] ta = new IloNumVar[data.nNodes];
                            if (openedhubs.contains(ori)) {
                                x[ori][ori] = cpx.intVar(0, 1, "x(" + ori + "," + ori + ")");
                            } else {
                                for (int n : openedhubs) {
                                    x[ori][n] = cpx.intVar(0, 1, "x(" + ori + "," + n + ")");
                                }
                            }

                            if (openedhubs.contains(des)) {
                                x[des][des] = cpx.intVar(0, 1, "x(" + des + "," + des + ")");
                            } else {
                                for (int n_ : openedhubs) {
                                    x[n_][des] = cpx.intVar(0, 1, "x(" + n_ + "," + des + ")");
                                }
                            }

                            for (int n : openedhubs) {
                                for (int n_ : openedhubs) {
                                    if (n != n_) {
                                        x[n][n_] = cpx.intVar(0, 1, "x(" + n + "," + n_ + ")");
                                    }
                                }
                            }
                            for (int n : openedhubs) {
                                ta[n] = cpx.numVar(0, Double.MAX_VALUE, "ta(" + n + ")");
                            }
                            IloLinearNumExpr cpxObj = cpx.linearNumExpr();
                            if (openedhubs.contains(ori)) {
                                cpxObj.addTerm(cnn[ori][ori], x[ori][ori]);
                            } else {
                                for (int n : openedhubs) {
                                    cpxObj.addTerm(cnn[ori][n], x[ori][n]);
                                }
                            }

                            if (openedhubs.contains(des)) {
                                cpxObj.addTerm(cnn[des][des], x[des][des]);
                            } else {
                                for (int n_ : openedhubs) {
                                    cpxObj.addTerm(cnn[n_][des], x[n_][des]);
                                }
                            }

                            for (int n : openedhubs) {
                                for (int n_ : openedhubs) {
                                    if (n != n_) {
                                        cpxObj.addTerm(cnn[n][n_], x[n][n_]);
                                    }
                                }
                            }
                            cpx.addMinimize(cpxObj);
                            //constraint1
                            IloLinearNumExpr const1 = cpx.linearNumExpr();
                            if (openedhubs.contains(ori)) {
                                const1.addTerm(1, x[ori][ori]);
                            } else {
                                for (int n : openedhubs) {
                                    const1.addTerm(1, x[ori][n]);
                                }
                            }
                            if (openedhubs.contains(des)) {
                                const1.addTerm(1, x[des][des]);
                            } else {
                                for (int n_ : openedhubs) {
                                    const1.addTerm(1, x[n_][des]);
                                }
                            }

                            for (int n : openedhubs) {
                                for (int n_ : openedhubs) {
                                    if (n != n_) {
                                        const1.addTerm(1, x[n][n_]);
                                    }
                                }
                            }
                            cpx.addLe(const1, data.Path_Length_Limit + m, "const1");

                            //Constraint 2
                            IloLinearNumExpr ori_h = cpx.linearNumExpr();
                            if (openedhubs.contains(ori)) {
                                ori_h.addTerm(1, x[ori][ori]);
                            } else {
                                for (int n_ : openedhubs) {
                                    ori_h.addTerm(1, x[ori][n_]);
                                }
                            }
                            cpx.addEq(ori_h, 1, "const2_ori_h(" + ori + ")");

                            IloLinearNumExpr h_des = cpx.linearNumExpr();
                            if (openedhubs.contains(des)) {
                                h_des.addTerm(1, x[des][des]);
                            } else {
                                for (int n_ : openedhubs) {
                                    h_des.addTerm(1, x[n_][des]);
                                }
                            }
                            cpx.addEq(h_des, 1, "const2_h_des(" + des + ")");

                            IloLinearNumExpr[] const2 = new IloLinearNumExpr[data.nNodes];
                            for (int n : openedhubs) {
                                const2[n] = cpx.linearNumExpr();
                                const2[n].addTerm(1, x[n][des]);
                                for (int n_ : openedhubs) {
                                    if (n != n_) {
                                        if (n_ != des) {
                                            const2[n].addTerm(1, x[n][n_]);
                                        }
                                        if (n_ != ori) {
                                            const2[n].addTerm(-1, x[n_][n]);
                                        }
                                    }
                                }
                                const2[n].addTerm(-1, x[ori][n]);
                                cpx.addEq(const2[n], 0, "const2(" + n + ")");
                            }

                            //Constraint3
                            IloLinearNumExpr[][] const3 = new IloLinearNumExpr[data.nNodes][data.nNodes];
                            for (int n : openedhubs) {
                                for (int n_ : openedhubs) {
                                    if (n != n_) {
                                        const3[n][n_] = cpx.linearNumExpr();
                                        const3[n][n_].addTerm(1, ta[n]);
                                        const3[n][n_].addTerm(-1, ta[n_]);
                                        const3[n][n_].addTerm(openedhubs.size(), x[n][n_]);
                                        cpx.addLe(const3[n][n_], openedhubs.size() - 1, "const3(" + n + "," + n_ + ")");
                                    }
                                }
                            }
                            cpx.solve();
                            if (cpx.getObjValue() < -1E-6) {
                                cg = true;
                                ArrayList<int[]> hub_hub = new ArrayList<>();
                                ArrayList<Integer> hubs = new ArrayList<>();
                                int[] h_h = new int[2];
                                int[] n_h = new int[2];
                                int[] h_n = new int[2];
                                System.out.println("negatif reduced cost is found! k:" + k + " ___ " + ori + "->" + des + "   -- it: " + iteration + "_" + loop);
                                boolean ori_ori = false;
                                boolean des_des = false;
                                if (openedhubs.contains(ori)) {
                                    if (cpx.getValue(x[ori][ori]) > 0) {
                                        ori_ori = true;
                                        n_h[0] = ori;
                                        n_h[1] = ori;
                                        System.out.println("x(" + ori + "," + ori + ")");
                                        //System.out.println("w:" + data.W[k]);
                                        //System.out.println("cnn(" + ori + "," + ori + "): " + cnn[ori][ori]);
                                    }
                                } else {
                                    for (int n : openedhubs) {
                                        if (cpx.getValue(x[ori][n]) > 0) {
                                            n_h[0] = ori;
                                            n_h[1] = n;
                                            System.out.println("x(" + ori + "," + n + ")");
                                            //System.out.println("w:" + data.W[k]);
                                            //System.out.println("cnn(" + ori + "," + n + "): " + cnn[ori][n]);
                                        }
                                    }
                                }

                                for (int n : openedhubs) {
                                    for (int n_ : openedhubs) {
                                        if (n != n_) {
                                            if (cpx.getValue(x[n][n_]) > 0) {
                                                h_h[0] = n;
                                                h_h[1] = n_;
                                                hub_hub.add(h_h);
                                                h_h = new int[2];
                                                System.out.println("x(" + n + "," + n_ + ")");
                                                //System.out.println("w:" + data.W[k]);
                                                //System.out.println("cnn(" + n + "," + n_ + "): " + cnn[n][n_]);
                                            }
                                        }
                                    }
                                }
                                if (openedhubs.contains(des)) {
                                    if (cpx.getValue(x[des][des]) > 0) {
                                        des_des = true;
                                        h_n[0] = des;
                                        h_n[1] = des;
                                        System.out.println("x(" + des + "," + des + ")");
                                        //System.out.println("w:" + data.W[k]);
                                        //System.out.println("cnn(" + des + "," + des + "): " + cnn[des][des]);
                                    }
                                } else {
                                    for (int n : openedhubs) {
                                        if (cpx.getValue(x[n][des]) > 0) {
                                            h_n[0] = n;
                                            h_n[1] = des;
                                            System.out.println("x(" + n + "," + des + ")");
                                            //System.out.println("w:" + data.W[k]);
                                            //System.out.println("cnn(" + n + "," + des + "): " + cnn[n][des]);
                                        }
                                    }
                                }

                                System.out.println(cpx.getObjValue());
                                //cpx.exportModel("it" + iteration + "_" + loop + "_cpx" + k + ".lp");
                                //cpx.writeSolution("it" + iteration + "_" + loop + "_sol_cpx" + k + ".lp");

                                String path = "newp#";
                                path = path + n_h[0] + "_" + n_h[1];
                                int s = n_h[1];
                                hubs.add(s);
                                while (hub_hub.size() > 0) {
                                    for (int g = 0; g < hub_hub.size(); g++) {
                                        int[] a = hub_hub.get(g);
                                        if (s == a[0]) {
                                            s = a[1];
                                            hubs.add(s);
                                            path = path + "_" + s;
                                            hub_hub.remove(a);
                                        }
                                    }
                                }
                                path = path + "_" + h_n[1];

                                double cost = 0;
                                cost = cost + data.Collection_Coeff * data.C[t][n_h[0]][n_h[1]];

                                for (int h : hubs) {
                                    if (h == n_h[1]) {
                                        s = n_h[1];
                                    } else {
                                        cost = cost + data.alpha * data.C[t][s][h];
                                        s = h;
                                    }
                                }
                                cost = cost + data.Distribution_Coeff * data.C[t][h_n[0]][h_n[1]];
                                cost = cost * data.W[t][k];
                                IloNumVar newpathvar = sp[t].sub.numVar(0, Double.MAX_VALUE, path);
                                sp[t].subObj.addTerm(cost, newpathvar);
                                sp[t].SubObjFunc.setExpr(sp[t].subObj);
                                sp[t].subconst1[k].addTerm(1, newpathvar);
                                sp[t].demandSatisy[k].setExpr(sp[t].subconst1[k]);
                                for (int h : hubs) {
                                    sp[t].subconst2[h].addTerm(data.W[t][k], newpathvar);
                                    sp[t].Flow[h].setExpr(sp[t].subconst2[h]);
                                    sp[t].subconst3[k][h].addTerm(1, newpathvar);
                                    sp[t].OpenedhubDemand[k][h].setExpr(sp[t].subconst3[k][h]);
                                }
                                if (ori_ori) {
                                    sp[t].subconst4[k].addTerm(1, newpathvar);
                                    sp[t].originfirsthub[k].setExpr(sp[t].subconst4[k]);
                                }
                                if (des_des) {
                                    sp[t].subconst5[k].addTerm(1, newpathvar);
                                    sp[t].destlasthub[k].setExpr(sp[t].subconst5[k]);
                                }
                            }
                        }*/
            } else {//Labeling
              for (int k = 0; k < data.num_od; k++) {
                double[][] cnn = new double[data.nNodes][data.nNodes];
                int ori = data.k_od.get(k)[0];
                int des = data.k_od.get(k)[1];

                if (data.candhubs.contains(ori)) {
                  cnn[ori][ori] = data.W[t][sc][k] * data.C[t][ori][ori] * data.Collection_Coeff
                      - dual_demandSatisy[t][k] - data.W[t][sc][k] * dual_Flow[t][ori]
                      - dual_OpenedhubDemand[t][k][ori] - dual_originfirsthub[t][k];
                } else {
                  for (int n : data.candhubs) {
                    cnn[ori][n] = data.W[t][sc][k] * data.C[t][ori][n] * data.Collection_Coeff
                        - dual_demandSatisy[t][k] - data.W[t][sc][k] * dual_Flow[t][n]
                        - dual_OpenedhubDemand[t][k][n];
                  }
                }

                if (data.candhubs.contains(des)) {
                  cnn[des][des] = data.W[t][sc][k] * data.C[t][des][des] * data.Distribution_Coeff
                      - dual_destlasthub[t][k];
                } else {
                  for (int n_ : data.candhubs) {
                    cnn[n_][des] = data.W[t][sc][k] * data.C[t][n_][des] * data.Distribution_Coeff;
                  }
                }

                for (int n : data.candhubs) {
                  for (int n_ : data.candhubs) {
                    if (n != n_) {
                      cnn[n][n_] = data.W[t][sc][k] * data.C[t][n][n_] * data.alpha
                          - data.W[t][sc][k] * dual_Flow[t][n_] - dual_OpenedhubDemand[t][k][n_];
                    }
                  }
                }
                Label L = new Label();
                L.n = ori;
                L.c = 0;
                L.l = data.Path_Length_Limit;
                L.N = new ArrayList<>(data.candhubs);
                L.hubs = new ArrayList();
                L.path = "newp#" + ori;

                if (data.candhubs.contains(ori)) {
                  L.N.remove(Integer.valueOf(ori));
                  L.c = L.c + cnn[ori][ori];
                  L.path = L.path + "_" + ori;
                  L.hubs.add(ori);
                }
                if (data.candhubs.contains(des)) {
                  L.N.remove(Integer.valueOf(des));
                  L.c = L.c + cnn[des][des];
                }
                ArrayList<Label>[] Labels = new ArrayList[data.nNodes];
                //first expansion
                for (int n : L.N) {
                  Labels[n] = new ArrayList<>();
                  Label L_ = new Label();
                  L_.n = n;
                  L_.c = L.c + cnn[ori][n];
                  L_.N = new ArrayList<>(L.N);
                  L_.N.remove(Integer.valueOf(n));
                  L_.hubs = new ArrayList<>(L.hubs);
                  L_.hubs.add(n);
                  L_.path = L.path;
                  L_.path = L_.path + "_" + n;
                  L_.l = L.l - 1;
                  Labels[n].add(L_);
                }
                L.processed = true;

                boolean devam = true;
                ArrayList<Label>[] NewAdddedLabels = new ArrayList[data.nNodes];
                for (int n : L.N) {
                  NewAdddedLabels[n] = new ArrayList<>();
                }

                while (devam) {
                  devam = false;
                  for (int n : L.N) {
                    for (Label lab : Labels[n]) {
                      if (lab.l - 1 >= 1 & lab.processed == false & lab.N.size() > 0) {
                        for (int n_ : lab.N) {
                          Label L_ = new Label();
                          L_.c = lab.c + cnn[lab.n][n_];
                          L_.n = n_;
                          L_.N = new ArrayList<>(lab.N);
                          L_.N.remove(Integer.valueOf(n_));
                          L_.hubs = new ArrayList<>(lab.hubs);
                          L_.hubs.add(n_);
                          L_.path = lab.path + "_" + n_;
                          L_.l = lab.l - 1;
                          NewAdddedLabels[n_].add(L_);
                        }
                        lab.processed = true;
                        devam = true;
                      }
                    }
                  }
                  //elimination
                  for (int n : L.N) {
                    for (Label lab1 : Labels[n]) {
                      for (Label lab2 : NewAdddedLabels[n]) {
                        if (lab1.c < lab2.c) {
                          lab2.processed = true;
                        }
                      }
                    }
                  }
                  //add new labels
                  for (int n : L.N) {
                    for (Label lab : NewAdddedLabels[n]) {
                      Labels[n].add(lab);
                    }
                  }
                  //reset
                  for (int n : L.N) {
                    NewAdddedLabels[n] = new ArrayList<>();
                  }
                }
                //last arc
                for (int n : L.N) {
                  for (Label lab : Labels[n]) {
                    lab.c = lab.c + cnn[lab.n][des];
                    lab.path = lab.path + "_" + des;
                    if (data.candhubs.contains(des)) {
                      lab.path = lab.path + "_" + des;
                      lab.hubs.add(des);
                    }
                  }
                }

                if (data.candhubs.contains(ori) && data.candhubs.contains(des)) {
                  L.N.add(ori);
                  Label onearc = new Label();
                  onearc.c = cnn[ori][ori] + cnn[ori][des] + cnn[des][des];
                  onearc.hubs = new ArrayList();
                  onearc.hubs.add(ori);
                  onearc.hubs.add(des);
                  onearc.path = "p#" + ori + "_" + ori + "_" + des + "_" + des;
                  Labels[ori] = new ArrayList<>();
                  Labels[ori].add(onearc);
                }
                if (data.candhubs.contains(ori) && !data.candhubs.contains(des)) {
                  L.N.add(ori);
                  Label onearc = new Label();
                  onearc.c = cnn[ori][ori] + cnn[ori][des];
                  onearc.hubs = new ArrayList();
                  onearc.hubs.add(ori);
                  onearc.path = "p#" + ori + "_" + ori + "_" + des;
                  Labels[ori] = new ArrayList<>();
                  Labels[ori].add(onearc);
                }
                if (!data.candhubs.contains(ori) && data.candhubs.contains(des)) {
                  L.N.add(des);
                  Label onearc = new Label();
                  onearc.c = cnn[ori][des] + cnn[des][des];
                  onearc.hubs = new ArrayList();
                  onearc.hubs.add(des);
                  onearc.path = "p#" + ori + "_" + des + "_" + des;
                  Labels[des] = new ArrayList<>();
                  Labels[des].add(onearc);
                }

                for (int n : L.N) {
                  for (Label lab : Labels[n]) {
                    if ((lab.c < -1E-4) & (sp[t][sc].k_paths.get(k).contains(lab.path) == false)) {
                      double cost = 0;
                      double arctimes = 0;
                      double congtimes = 0;
                      int h1 = lab.hubs.get(0);
                      int s = h1;
                      cost = cost + data.Collection_Coeff * data.C[t][ori][h1];
                      arctimes = data.time[t][ori][h1];
                      for (int h : lab.hubs) {
                        for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
                          congtimes = congtimes
                              + getValue(z[t][sc][h][caplev]) * data.delta_z * r_value[h][caplev];
                        }
                        if (h == h1) {
                          s = h1;
                        } else {
                          cost = cost + data.alpha * data.C[t][s][h];
                          arctimes = arctimes + data.time[t][s][h];
                          s = h;
                        }
                      }
                      cost = cost + data.Distribution_Coeff * data.C[t][s][des];
                      if (arctimes + congtimes <= data.Tmin[t][k]) {
                        cg = true;
                        //System.out.println("--------New route found!" + " k:" + k + "    " + ori + "->" + des);
                        //System.out.println(lab.path + "   reduced cost: " + lab.c);
                        //System.out.println("--------------------------");
                        addedpaths =
                            addedpaths + "iteration: " + iteration + "__k:" + k + "__" + ori + "->"
                                + des + "\n";
                        addedpaths = addedpaths + lab.path + "   reduced cost: " + lab.c + "\n";
                        addedpaths = addedpaths + "--------------------------" + "\n";
                        if (cost > data.bigM) {
                          sp[t][sc].InfeasiblePaths.add(lab.path);
                        }
                        cost = cost * data.W[t][sc][k];
                        IloNumVar newpathvar = sp[t][sc].sub.numVar(0, Double.MAX_VALUE, lab.path);
                        sp[t][sc].path_candhubs.put(lab.path, lab.hubs);
                        sp[t][sc].k_paths.get(k).add(lab.path);
                        sp[t][sc].path_vars.put(lab.path, newpathvar);
                        sp[t][sc].path_time.put(lab.path, arctimes);
                        sp[t][sc].path_cost.put(lab.path, cost);
                        sp[t][sc].path_k.put(lab.path, k);
                        addedPathCounter = addedPathCounter + 1;
                        sp[t][sc].subObj.addTerm(data.pr[t][sc] * cost, newpathvar);
                        sp[t][sc].SubObjFunc.setExpr(sp[t][sc].subObj);
                        sp[t][sc].subconst1[k].addTerm(1, newpathvar);
                        sp[t][sc].demandSatisy[k].setExpr(sp[t][sc].subconst1[k]);
                        for (int h : lab.hubs) {
                          sp[t][sc].subconst2[h].addTerm(data.W[t][sc][k], newpathvar);
                          sp[t][sc].Flow[h].setExpr(sp[t][sc].subconst2[h]);
                          sp[t][sc].subconst3[k][h].addTerm(1, newpathvar);
                          sp[t][sc].OpenedhubDemand[k][h].setExpr(sp[t][sc].subconst3[k][h]);
                        }
                        if (data.candhubs.contains(ori)) {
                          sp[t][sc].subconst4[k].addTerm(1, newpathvar);
                          sp[t][sc].originfirsthub[k].setExpr(sp[t][sc].subconst4[k]);
                        }
                        if (data.candhubs.contains(des)) {
                          sp[t][sc].subconst5[k].addTerm(1, newpathvar);
                          sp[t][sc].destlasthub[k].setExpr(sp[t][sc].subconst5[k]);
                        }

                      }


                    }
                  }
                }
              }

              ArrayList<String> DeletedPaths = new ArrayList<>();
              for (String p : sp[t][sc].path_vars.keySet()) {
                double totaltime = 0;
                int numusedHub = 0;
                totaltime = totaltime + sp[t][sc].path_time.get(p);
                for (int h : sp[t][sc].path_candhubs.get(p)) {
                  for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
                    totaltime = totaltime
                        + getValue(z[t][sc][h][caplev]) * data.delta_z * r_value[h][caplev];
                  }
                  numusedHub = numusedHub + 1;
                }
                if (totaltime > data.Tmin[t][sp[t][sc].path_k.get(p)]) {
                  if (data.print) {
                    System.out.println("(" + t + "," + sc + ")" +
                        p + " is deleted!!!  " + "Arctime: " + sp[t][sc].path_time.get(p)
                        + " congTime: " + (totaltime - sp[t][sc].path_time.get(p)) + " Tmin: "
                        + data.Tmin[t][sp[t][sc].path_k.get(p)]);
                  }
                  cg = true;
                  DeletedPaths.add(p);
                }
              }
              for (String p : DeletedPaths) {
                //pathi SP'den de çıkar
                sp[t][sc].sub.delete(sp[t][sc].path_vars.get(p));
                sp[t][sc].path_k.remove(p);
                sp[t][sc].path_candhubs.remove(p);
                sp[t][sc].path_vars.remove(p);
                sp[t][sc].path_cost.remove(p);
                deletedPathCounter = deletedPathCounter + 1;
                for (int k = 0; k < data.num_od; k++) {
                  if (sp[t][sc].k_paths.get(k).contains(p)) {
                    sp[t][sc].k_paths.get(k).remove(p);
                    break;
                  }
                }
              }
            }

            if (cg) {
              //sp[t].sub.exportModel("it" + iteration + "_" + loop + "_sub_addedpaths.lp");
              if (data.print) {
                System.out.println("found paths are added---------");
              }
              sp[t][sc].sub.solve();
            }
          }

          IloNumExpr[][] expr = new IloNumExpr[data.nPeriod + 1][data.maxnumsce];
          expr[t][sc] = master.numExpr();
          double[][] expr_value = new double[data.nPeriod + 1][data.maxnumsce];
          expr_value[t][sc] = 0;

          for (int k = 0; k < data.num_od; k++) {
            expr[t][sc] = master.sum(expr[t][sc],
                master.prod(dual_demandSatisy[t][k], sp[t][sc].rhs.get(sp[t][sc].demandSatisy[k])));
            expr_value[t][sc] = expr_value[t][sc] + dual_demandSatisy[t][k] * getValue(
                sp[t][sc].rhs.get(sp[t][sc].demandSatisy[k]));
          }

          for (int h : data.candhubs) {
            for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
              expr[t][sc] = master.sum(expr[t][sc],
                  master.prod(dual_CapacityFlow[t][h][caplev],
                      sp[t][sc].rhs.get(sp[t][sc].CapacityFlow[h][caplev])));
              expr_value[t][sc] = expr_value[t][sc] + dual_CapacityFlow[t][h][caplev] * getValue(
                  sp[t][sc].rhs.get(sp[t][sc].CapacityFlow[h][caplev]));
            }
          }

          for (int k = 0; k < data.num_od; k++) {
            for (int h : data.candhubs) {
              expr[t][sc] = master.sum(expr[t][sc], master.prod(dual_OpenedhubDemand[t][k][h],
                  sp[t][sc].rhs.get(sp[t][sc].OpenedhubDemand[k][h])));
              expr_value[t][sc] = expr_value[t][sc] + dual_OpenedhubDemand[t][k][h] * getValue(
                  sp[t][sc].rhs.get(sp[t][sc].OpenedhubDemand[k][h]));
            }
          }

          for (int k = 0; k < data.num_od; k++) {
            if (sp[t][sc].a[k] == 1) {
              expr[t][sc] = master.sum(expr[t][sc], master
                  .prod(dual_originfirsthub[t][k], sp[t][sc].rhs.get(sp[t][sc].originfirsthub[k])));
              expr_value[t][sc] = expr_value[t][sc] + dual_originfirsthub[t][k] * getValue(
                  sp[t][sc].rhs.get(sp[t][sc].originfirsthub[k]));
            }
          }

          for (int k = 0; k < data.num_od; k++) {
            if (sp[t][sc].b[k] == 1) {
              expr[t][sc] = master.sum(expr[t][sc],
                  master.prod(dual_destlasthub[t][k], sp[t][sc].rhs.get(sp[t][sc].destlasthub[k])));
              expr_value[t][sc] = expr_value[t][sc] + dual_destlasthub[t][k] * getValue(
                  sp[t][sc].rhs.get(sp[t][sc].destlasthub[k]));
            }
          }

          for (int h : data.candhubs) {
            for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
              expr[t][sc] = master.sum(expr[t][sc],
                  master.prod(dual_socp2[t][h][caplev],
                      sp[t][sc].rhs.get(sp[t][sc].socp2range[h][caplev])));
              expr_value[t][sc] = expr_value[t][sc] + dual_socp2[t][h][caplev] * getValue(
                  sp[t][sc].rhs.get(sp[t][sc].socp2range[h][caplev]));
            }
          }

          for (int h : data.candhubs) {
            for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
              expr[t][sc] = master.sum(expr[t][sc],
                  master.prod(dual_socp3[t][h][caplev],
                      sp[t][sc].rhs.get(sp[t][sc].socp3range[h][caplev])));
              expr_value[t][sc] = expr_value[t][sc] + dual_socp3[t][h][caplev] * getValue(
                  sp[t][sc].rhs.get(sp[t][sc].socp3range[h][caplev]));
            }
          }

          //sp[t][sc].sub.exportModel(t +"_"+sc + "_sub" + iteration + ".lp");
          if (Math.abs(expr_value[t][sc] - sp[t][sc].sub.getObjValue()) > 0.5) {
            System.out.println("Ohm(" + t + "," + sc + "): " + getValue(ohm[t][sc]));
            System.out.println("expr_value(" + t + "," + sc + "): " + expr_value[t][sc]);
            System.out.println("sub(" + t + "," + sc + "): " + sp[t][sc].sub.getObjValue());
            System.out.println("!!!");

            File f = new File(
                resultsFilePath + "unsolvedcase_" + data.paramfp + "_" + data.datafp + ".txt");
            /* create a new file if not exists */
            if (!f.exists()) {
              try (var fw = new FileWriter(f);
                  var bw = new BufferedWriter(fw)) {
                bw.write("iteration: " + iteration + "  t:" + t + "  sc:" + sc + "  exprde sorun");
              } catch (IOException e) {
                e.printStackTrace();
              }
            }
            try (var fw = new FileWriter(f, true);
                var bw = new BufferedWriter(fw)) {
              bw.write("iteration: " + iteration + "  t:" + t + "  sc:" + sc + "  exprde sorun");
            } catch (IOException e) {
              e.printStackTrace();
            }
          }
          if (cont_sub_failed) {
            IloRange r = add(
                (IloRange) master.ge(ohm[t][sc], expr[t][sc]));  // add teta>= expression to master
            OptCutCounter = OptCutCounter + 1;
            if (data.print) {
              System.out
                  .println("\n>>> Adding optimality cut: " + r + "\n"); //print the optimality cut
            }
          }
        }
      }
    }
  }
}


class Label {

  int n;
  double c;
  int l;
  ArrayList<Integer> N;
  ArrayList<Integer> hubs;
  String path;
  boolean processed = false;
}