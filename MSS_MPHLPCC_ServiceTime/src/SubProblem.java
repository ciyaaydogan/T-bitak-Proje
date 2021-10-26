import ilog.concert.IloConstraint;
import ilog.concert.IloException;
import ilog.concert.IloIntVar;
import ilog.concert.IloLinearNumExpr;
import ilog.concert.IloNumExpr;
import ilog.concert.IloNumVar;
import ilog.concert.IloObjective;
import ilog.concert.IloRange;
import ilog.cplex.IloCplex;
import java.util.ArrayList;
import java.util.HashMap;

public class SubProblem {

  IloNumVar ohm;
  Data data;
  IloCplex master;
  IloCplex sub;
  IloNumVar[] v;
  IloNumVar[][] u;
  IloNumVar[][] z;
  IloNumVar[] y;
  IloNumVar[][] r;
  IloNumVar[][] tvar;
  IloNumVar[][] tneg;
  IloNumVar[][] tpos;
  IloObjective SubObjFunc;
  IloLinearNumExpr subObj;
  IloLinearNumExpr[] subconst1;
  IloLinearNumExpr[] subconst2;
  IloLinearNumExpr[][] subconst3;
  IloLinearNumExpr[] subconst4;
  IloLinearNumExpr[] subconst5;
  IloRange[] demandSatisy;
  IloRange[] Flow;
  IloRange[][] CapacityFlow;
  IloRange[][] OpenedhubDemand;
  IloRange[] originfirsthub;
  IloRange[] destlasthub;
  IloRange[][] socp2range;
  IloRange[][] socp3range;
  int[] a;
  int[] b;
  int t;
  int sc;
  HashMap<Integer, ArrayList<String>> k_paths;
  HashMap<String, Integer> path_k;
  HashMap<String, ArrayList<Integer>> path_candhubs;
  HashMap<String, IloNumVar> path_vars;
  HashMap<IloNumVar, IloNumVar> dummy_path_vars;
  HashMap<IloConstraint, IloNumExpr> rhs;
  HashMap<String, Double> path_cost;
  HashMap<String, Double> path_time;
  ArrayList<String> InfeasiblePaths;

  SubProblem(Data data, IloNumVar[][] z, IloIntVar[] y, IloCplex master, IloNumVar ohm, int t,
      int sc) throws IloException {
    this.data = data;
    this.master = master;
    this.z = z;
    this.y = y;
    this.ohm = ohm;
    this.t = t;
    this.sc = sc;
    InfeasiblePaths = new ArrayList<>();

    CreteInitialPaths();
    findpathcosts();
    findpathtimes();
    CreateSP(data, z, y, master, t, sc);
  }

  void CreateSP(Data data, IloNumVar[][] z, IloNumVar[] y, IloCplex master, int t, int sc)
      throws IloException {
    sub = new IloCplex();
    //define path variables
    v = new IloNumVar[2 * path_candhubs.size()];
    path_vars = new HashMap<>();
    dummy_path_vars = new HashMap<>();
    int i = 0;
    for (String p : path_candhubs.keySet()) {
      v[i] = sub.numVar(0.00, Double.MAX_VALUE, p);
      v[i + path_candhubs.size()] = sub.numVar(0.00, Double.MAX_VALUE, "dummy" + p);
      path_vars.put(p, v[i]);
      dummy_path_vars.put(v[i], v[i + path_candhubs.size()]);
      InfeasiblePaths.add(("dummy" + p));
      i = i + 1;
    }
    u = new IloNumVar[data.nNodes][data.Num_Cap_Levels + 1];
    for (int h : data.candhubs) {
      for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
        u[h][caplev] = sub.numVar(0, Double.MAX_VALUE, "u(" + h + "," + caplev + ")");
      }
    }
    r = new IloNumVar[path_candhubs.size()][data.Num_Cap_Levels + 1];
    for (int h : data.candhubs) {
      for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
        r[h][caplev] = sub.numVar(0.00, Double.MAX_VALUE, "r(" + h + "," + caplev + ")");
      }
    }
    tvar = new IloNumVar[path_candhubs.size()][data.Num_Cap_Levels + 1];
    for (int h : data.candhubs) {
      for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
        tvar[h][caplev] = sub.numVar(0, Double.MAX_VALUE, "t(" + h + "," + caplev + ")");
      }
    }
    tneg = new IloNumVar[path_candhubs.size()][data.Num_Cap_Levels + 1];
    for (int h : data.candhubs) {
      for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
        tneg[h][caplev] = sub
            .numVar(-1 * Double.MAX_VALUE, Double.MAX_VALUE, "tneg(" + h + "," + caplev + ")");
      }

    }
    tpos = new IloNumVar[path_candhubs.size()][data.Num_Cap_Levels + 1];
    for (int h : data.candhubs) {
      for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
        tpos[h][caplev] = sub.numVar(0.00, Double.MAX_VALUE, "tpos(" + h + "," + caplev + ")");
      }

    }

    //define sub obj function
    subObj = sub.linearNumExpr();
    for (int k = 0; k < data.num_od; k++) {
      for (String p : k_paths.get(k)) {
        subObj.addTerm(data.pr[t][sc] * path_cost.get(p), path_vars.get(p));
        subObj.addTerm(data.bigM, dummy_path_vars.get(path_vars.get(p)));
      }
    }
    for (int h : data.candhubs) {
      for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
        subObj.addTerm(data.pr[t][sc] * data.b, r[h][caplev]);
      }

    }
    SubObjFunc = sub.minimize(subObj);
    sub.add(SubObjFunc);

    //define demand satisfying constraints for each o_d
    rhs = new HashMap<>();
    demandSatisy = new IloRange[data.num_od];
    subconst1 = new IloLinearNumExpr[data.num_od];
    for (int k = 0; k < data.num_od; k++) {
      subconst1[k] = sub.linearNumExpr();
      for (String p : k_paths.get(k)) {
        subconst1[k].addTerm(1, path_vars.get(p));
        subconst1[k].addTerm(1, dummy_path_vars.get(path_vars.get(p)));
      }
      demandSatisy[k] = sub.addGe(subconst1[k], 1,
          "demandSatisfy(" + data.k_od.get(k)[0] + "," + data.k_od.get(k)[1] + ")");
      rhs.put(demandSatisy[k], master.linearNumExpr(1));
    }
    //define flow constraints
    Flow = new IloRange[data.nNodes];
    subconst2 = new IloLinearNumExpr[data.nNodes];
    for (int h : data.candhubs) {
      subconst2[h] = sub.linearNumExpr();
      for (int k = 0; k < data.num_od; k++) {
        for (String p : k_paths.get(k)) {
          if (path_candhubs.get(p).contains(h)) {
            subconst2[h].addTerm(data.W[this.t][this.sc][k], path_vars.get(p));
            subconst2[h].addTerm(data.W[this.t][this.sc][k], dummy_path_vars.get(path_vars.get(p)));
          }
        }
      }
      for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
        subconst2[h].addTerm(-1, u[h][caplev]);
      }

      Flow[h] = sub.addLe(subconst2[h], 0, "Flow(" + h + ")");
      rhs.put(Flow[h], master.linearNumExpr(0));
    }
    //define capacity constraints
    IloLinearNumExpr[][] CapacityFlowRhs = new IloLinearNumExpr[data.nNodes][data.Num_Cap_Levels
        + 1];
    IloLinearNumExpr[][] CapacityFlowLhs = new IloLinearNumExpr[data.nNodes][data.Num_Cap_Levels
        + 1];
    CapacityFlow = new IloRange[data.nNodes][data.Num_Cap_Levels + 1];
    for (int h : data.candhubs) {
      for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
        CapacityFlowLhs[h][caplev] = sub.linearNumExpr();
        CapacityFlowLhs[h][caplev].addTerm(data.CongCoef, u[h][caplev]);
        CapacityFlow[h][caplev] = sub
            .addLe(CapacityFlowLhs[h][caplev], 0, "CapacityFlow(" + h + "," + caplev + ")");
        CapacityFlowRhs[h][caplev] = sub.linearNumExpr();
        CapacityFlowRhs[h][caplev].addTerm(data.K[h][caplev], z[h][caplev]);
        rhs.put(CapacityFlow[h][caplev], CapacityFlowRhs[h][caplev]);
      }
    }
    //define openedhub-demand constraints
    OpenedhubDemand = new IloRange[data.num_od][data.nNodes];
    subconst3 = new IloLinearNumExpr[data.num_od][data.nNodes];
    for (int k = 0; k < data.num_od; k++) {
      for (int h : data.candhubs) {
        subconst3[k][h] = sub.linearNumExpr();
        for (String p : k_paths.get(k)) {
          if (path_candhubs.get(p).contains(h)) {
            subconst3[k][h].addTerm(1, path_vars.get(p));
            subconst3[k][h].addTerm(1, dummy_path_vars.get(path_vars.get(p)));
          }
        }
        OpenedhubDemand[k][h] = sub.addLe(subconst3[k][h], 0,
            "OpenedhubDemand(" + data.k_od.get(k)[0] + "_" + data.k_od.get(k)[1] + "," + h + ")");
        rhs.put(OpenedhubDemand[k][h], master.prod(1, y[h]));
      }
    }

    //origin_first hub constraints
    a = new int[data.num_od];
    originfirsthub = new IloRange[data.num_od];
    subconst4 = new IloLinearNumExpr[data.num_od];
    for (int k = 0; k < data.num_od; k++) {
      a[k] = 0;
      subconst4[k] = sub.linearNumExpr();
      for (String p : k_paths.get(k)) {
        if ((path_candhubs.get(p).get(0) == data.k_od.get(k)[0])) {
          subconst4[k].addTerm(1, path_vars.get(p));
          subconst4[k].addTerm(1, dummy_path_vars.get(path_vars.get(p)));
          a[k] = 1;
        }
      }
      if (a[k] == 1) {
        originfirsthub[k] = sub.addEq(subconst4[k], 0,
            "originfirsthub(" + data.k_od.get(k)[0] + "_" + data.k_od.get(k)[1] + ")");
        rhs.put(originfirsthub[k], master.prod(1, y[data.k_od.get(k)[0]]));
      }
    }

    //destination_last hub constraints
    b = new int[data.num_od];
    destlasthub = new IloRange[data.num_od];
    subconst5 = new IloLinearNumExpr[data.num_od];
    for (int k = 0; k < data.num_od; k++) {
      b[k] = 0;
      subconst5[k] = sub.linearNumExpr();
      for (String p : k_paths.get(k)) {
        if ((path_candhubs.get(p).get(path_candhubs.get(p).size() - 1) == data.k_od.get(k)[1])) {
          subconst5[k].addTerm(1, path_vars.get(p));
          subconst5[k].addTerm(1, dummy_path_vars.get(path_vars.get(p)));
          b[k] = 1;
        }
      }
      if (b[k] == 1) {
        destlasthub[k] = sub.addEq(subconst5[k], 0,
            "destlasthub(" + data.k_od.get(k)[0] + "_" + data.k_od.get(k)[1] + ")");
        rhs.put(destlasthub[k], master.prod(1, y[data.k_od.get(k)[1]]));
      }
    }

    socp2range = new IloRange[data.nNodes][data.Num_Cap_Levels + 1];
    socp3range = new IloRange[data.nNodes][data.Num_Cap_Levels + 1];
    IloLinearNumExpr[][] socp1 = new IloLinearNumExpr[data.nNodes][data.Num_Cap_Levels + 1];
    IloLinearNumExpr[][] socp2 = new IloLinearNumExpr[data.nNodes][data.Num_Cap_Levels + 1];
    IloLinearNumExpr[][] socp3 = new IloLinearNumExpr[data.nNodes][data.Num_Cap_Levels + 1];

    for (int h : data.candhubs) {
      for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
        socp1[h][caplev] = sub.linearNumExpr();

        socp1[h][caplev].addTerm(2, u[h][caplev]);
        socp1[h][caplev].addTerm(-1, tvar[h][caplev]);
        sub.addEq(socp1[h][caplev], 0, "socp1(" + h + "," + caplev + ")");
      }

    }
    for (int h : data.candhubs) {
      for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
        socp2[h][caplev] = sub.linearNumExpr();
        socp3[h][caplev] = sub.linearNumExpr();

        socp2[h][caplev].addTerm(data.K[h][caplev], r[h][caplev]);
        socp2[h][caplev].addTerm(-1, tneg[h][caplev]);
        socp2range[h][caplev] = sub
            .addEq(socp2[h][caplev], data.K[h][caplev], "socp2(" + h + "," + caplev + ")");
        //socp2range[h][caplev] = sub.addEq(socp2[h][caplev], 0, "socp2(" + h + "," + caplev + ")");
        rhs.put(socp2range[h][caplev], master.linearNumExpr(data.K[h][caplev]));
      }
    }
    for (int h : data.candhubs) {
      for (int caplev = 1; caplev <= data.Num_Cap_Levels; caplev++) {
        socp3[h][caplev].addTerm(data.K[h][caplev], r[h][caplev]);
        socp3[h][caplev].addTerm(-2, u[h][caplev]);
        socp3[h][caplev].addTerm(-1, tpos[h][caplev]);
        socp3range[h][caplev] = sub
            .addEq(socp3[h][caplev], -data.K[h][caplev], "socp3(" + h + "," + caplev + ")");
        //socp3range[h][caplev] = sub.addEq(socp3[h], 0, "socp3(" + h + ")");
        rhs.put(socp3range[h][caplev], master.linearNumExpr(-data.K[h][caplev]));

        sub.addLe(sub.sum(sub.prod(tvar[h][caplev], tvar[h][caplev]),
            sub.prod(tneg[h][caplev], tneg[h][caplev]),
            sub.prod(-1, sub.prod(tpos[h][caplev], tpos[h][caplev]))), 0,
            "socp4(" + h + "," + caplev + ")");
      }
    }

    sub.exportModel("InitialSub_" + t + "_" + sc + ".lp");

  }

  void CreteInitialPaths() { // create all paths
    int l = 2;
    k_paths = new HashMap<>();
    path_k = new HashMap<>();
    path_candhubs = new HashMap<>();
    for (int k = 0; k < data.k_od.size(); k++) {
      int ori = data.k_od.get(k)[0];
      int des = data.k_od.get(k)[1];
      ArrayList<String> paths = new ArrayList<>();
      if (!data.candhubs.contains(ori) && !data.candhubs.contains(des)) {
        CreatePathsNN(k, l, ori, des, k_paths, path_candhubs, paths);
      }
      if (data.candhubs.contains(ori) && !data.candhubs.contains(des)) {
        CreatePathsHN(k, l, ori, des, k_paths, path_candhubs, paths);
      }
      if (!data.candhubs.contains(ori) && data.candhubs.contains(des)) {
        CreatePathsNH(k, l, ori, des, k_paths, path_candhubs, paths);
      }
      if (data.candhubs.contains(ori) && data.candhubs.contains(des)) {
        CreatePathsHH(k, l, ori, des, k_paths, path_candhubs, paths);
      }
    }

  }

  void CreatePathsNN(int k, int l, int ori, int des, HashMap<Integer, ArrayList<String>> k_paths,
      HashMap<String, ArrayList<Integer>> path_candhubs, ArrayList<String> paths) {
    String path;
    ArrayList<Integer> hub;

    if (l > 1) { //l=2
      for (int i : data.candhubs) {
        if (i != ori & i != des) {
          hub = new ArrayList<>();
          path = "p#" + ori + "_" + i + "_" + des;
          paths.add(path);
          path_k.put(path,k);
          hub.add(i);
          path_candhubs.put(path, hub);
        }
      }
    }
    if (l > 2) { //l=3
      for (int i : data.candhubs) {
        for (int ii : data.candhubs) {
          if (i != ori && i != des && i != ii && ii != ori && ii != des) {
            hub = new ArrayList<>();
            path = "p#" + ori + "_" + i + "_" + ii + "_" + des;
            paths.add(path);
            path_k.put(path,k);
            hub.add(i);
            hub.add(ii);
            path_candhubs.put(path, hub);
          }
        }
      }
    }
    if (l > 3) { //l=4
      for (int i : data.candhubs) {
        for (int ii : data.candhubs) {
          for (int iii : data.candhubs) {
            if (i != ori && i != des && i != ii && ii != ori && ii != des && iii != ori && iii != i
                && iii != ii && iii != des) {
              hub = new ArrayList<>();
              path = "p#" + ori + "_" + i + "_" + ii + "_" + iii + "_" + des;
              paths.add(path);
              path_k.put(path,k);
              hub.add(i);
              hub.add(ii);
              hub.add(iii);
              path_candhubs.put(path, hub);
            }
          }
        }
      }
    }
    if (l > 4) { //l=5
      for (int i : data.candhubs) {
        for (int ii : data.candhubs) {
          for (int iii : data.candhubs) {
            for (int iiii : data.candhubs) {
              if (i != ori && i != des && i != ii && ii != ori && ii != des && iii != ori
                  && iii != i && iii != ii && iii != des && iiii != ori && iiii != i && iiii != ii
                  && iiii != iii && iiii != des) {
                hub = new ArrayList<>();
                path = "p#" + ori + "_" + i + "_" + ii + "_" + iii + "_" + iiii + "_" + des;
                paths.add(path);
                path_k.put(path,k);
                hub.add(i);
                hub.add(ii);
                hub.add(iii);
                hub.add(iiii);
                path_candhubs.put(path, hub);
              }
            }
          }
        }
      }
    }

    k_paths.put(k, paths);
  }

  void CreatePathsHN(int k, int l, int ori, int des, HashMap<Integer, ArrayList<String>> k_paths,
      HashMap<String, ArrayList<Integer>> path_candhubs, ArrayList<String> paths) {
    String path;
    ArrayList<Integer> hub;
    //h1 is open
    hub = new ArrayList<>();
    path = "p#" + ori + "_" + ori + "_" + des;
    paths.add(path);
    path_k.put(path,k);
    hub.add(ori);
    path_candhubs.put(path, hub);
    if (l > 1) { //l=2
      for (int i : data.candhubs) {
        if (i != ori & i != des) {
          hub = new ArrayList<>();
          path = "p#" + ori + "_" + ori + "_" + i + "_" + des;
          paths.add(path);
          path_k.put(path,k);
          hub.add(ori);
          hub.add(i);
          path_candhubs.put(path, hub);
        }
      }
    }
    if (l > 2) { //l=3
      for (int i : data.candhubs) {
        for (int ii : data.candhubs) {
          if (i != ori && i != des && i != ii && ii != ori && ii != des) {
            hub = new ArrayList<>();
            path = "p#" + ori + "_" + ori + "_" + i + "_" + ii + "_" + des;
            paths.add(path);
            path_k.put(path,k);
            hub.add(ori);
            hub.add(i);
            hub.add(ii);
            path_candhubs.put(path, hub);
          }
        }
      }
    }
    if (l > 3) { //l=4
      for (int i : data.candhubs) {
        for (int ii : data.candhubs) {
          for (int iii : data.candhubs) {
            if (i != ori && i != des && i != ii && ii != ori && ii != des && iii != ori && iii != i
                && iii != ii && iii != des) {
              hub = new ArrayList<>();
              path = "p#" + ori + "_" + ori + "_" + i + "_" + ii + "_" + iii + "_" + des;
              paths.add(path);
              path_k.put(path,k);
              hub.add(ori);
              hub.add(i);
              hub.add(ii);
              hub.add(iii);
              path_candhubs.put(path, hub);
            }
          }
        }
      }
    }
    if (l > 4) { //l=5
      for (int i : data.candhubs) {
        for (int ii : data.candhubs) {
          for (int iii : data.candhubs) {
            for (int iiii : data.candhubs) {
              if (i != ori && i != des && i != ii && ii != ori && ii != des && iii != ori
                  && iii != i && iii != ii && iii != des && iiii != ori && iiii != i && iiii != ii
                  && iiii != iii && iiii != des) {
                hub = new ArrayList<>();
                path = "p#" + ori + "_" + ori + "_" + i + "_" + ii + "_" + iii + "_" + iiii + "_"
                    + des;
                paths.add(path);
                path_k.put(path,k);
                hub.add(ori);
                hub.add(i);
                hub.add(ii);
                hub.add(iii);
                hub.add(iiii);
                path_candhubs.put(path, hub);
              }
            }
          }
        }
      }
    }

    //h2 is close
    if (l > 1) { //l=2
      for (int i : data.candhubs) {
        if (i != ori & i != des) {
          hub = new ArrayList<>();
          path = "p#" + ori + "_" + i + "_" + des;
          paths.add(path);
          path_k.put(path,k);
          hub.add(i);
          path_candhubs.put(path, hub);
        }
      }
    }
    if (l > 2) { //l=3
      for (int i : data.candhubs) {
        for (int ii : data.candhubs) {
          if (i != ori && i != des && i != ii && ii != ori && ii != des) {
            hub = new ArrayList<>();
            path = "p#" + ori + "_" + i + "_" + ii + "_" + des;
            paths.add(path);
            path_k.put(path,k);
            hub.add(i);
            hub.add(ii);
            path_candhubs.put(path, hub);
          }
        }
      }
    }
    if (l > 3) { //l=4
      for (int i : data.candhubs) {
        for (int ii : data.candhubs) {
          for (int iii : data.candhubs) {
            if (i != ori && i != des && i != ii && ii != ori && ii != des && iii != ori && iii != i
                && iii != ii && iii != des) {
              hub = new ArrayList<>();
              path = "p#" + ori + "_" + i + "_" + ii + "_" + iii + "_" + des;
              paths.add(path);
              path_k.put(path,k);
              hub.add(i);
              hub.add(ii);
              hub.add(iii);
              path_candhubs.put(path, hub);
            }
          }
        }
      }
    }
    if (l > 4) { //l=5
      for (int i : data.candhubs) {
        for (int ii : data.candhubs) {
          for (int iii : data.candhubs) {
            for (int iiii : data.candhubs) {
              if (i != ori && i != des && i != ii && ii != ori && ii != des && iii != ori
                  && iii != i && iii != ii && iii != des && iiii != ori && iiii != i && iiii != ii
                  && iiii != iii && iiii != des) {
                hub = new ArrayList<>();
                path = "p#" + ori + "_" + i + "_" + ii + "_" + iii + "_" + iiii + "_" + des;
                paths.add(path);
                path_k.put(path,k);
                hub.add(i);
                hub.add(ii);
                hub.add(iii);
                hub.add(iiii);
                path_candhubs.put(path, hub);
              }
            }
          }
        }
      }
    }

    k_paths.put(k, paths);

  }

  void CreatePathsNH(int k, int l, int ori, int des, HashMap<Integer, ArrayList<String>> k_paths,
      HashMap<String, ArrayList<Integer>> path_candhubs, ArrayList<String> paths) {
    String path;
    ArrayList<Integer> hub;
    //h2 is open
    hub = new ArrayList<>();
    path = "p#" + ori + "_" + des + "_" + des;
    paths.add(path);
    path_k.put(path,k);
    hub.add(des);
    path_candhubs.put(path, hub);
    if (l > 1) { //l=2
      for (int i : data.candhubs) {
        if (i != ori & i != des) {
          hub = new ArrayList<>();
          path = "p#" + ori + "_" + i + "_" + des + "_" + des;
          paths.add(path);
          path_k.put(path,k);
          hub.add(i);
          hub.add(des);
          path_candhubs.put(path, hub);
        }
      }
    }
    if (l > 2) { //l=3
      for (int i : data.candhubs) {
        for (int ii : data.candhubs) {
          if (i != ori && i != des && i != ii && ii != ori && ii != des) {
            hub = new ArrayList<>();
            path = "p#" + ori + "_" + i + "_" + ii + "_" + des + "_" + des;
            paths.add(path);
            path_k.put(path,k);
            hub.add(i);
            hub.add(ii);
            hub.add(des);
            path_candhubs.put(path, hub);
          }
        }
      }
    }
    if (l > 3) { //l=4
      for (int i : data.candhubs) {
        for (int ii : data.candhubs) {
          for (int iii : data.candhubs) {
            if (i != ori && i != des && i != ii && ii != ori && ii != des && iii != ori && iii != i
                && iii != ii && iii != des) {
              hub = new ArrayList<>();
              path = "p#" + ori + "_" + i + "_" + ii + "_" + iii + "_" + des + "_" + des;
              paths.add(path);
              path_k.put(path,k);
              hub.add(i);
              hub.add(ii);
              hub.add(iii);
              hub.add(des);
              path_candhubs.put(path, hub);
            }
          }
        }
      }
    }
    if (l > 4) { //l=5
      for (int i : data.candhubs) {
        for (int ii : data.candhubs) {
          for (int iii : data.candhubs) {
            for (int iiii : data.candhubs) {
              if (i != ori && i != des && i != ii && ii != ori && ii != des && iii != ori
                  && iii != i && iii != ii && iii != des && iiii != ori && iiii != i && iiii != ii
                  && iiii != iii && iiii != des) {
                hub = new ArrayList<>();
                path = "p#" + ori + "_" + i + "_" + ii + "_" + iii + "_" + iiii + "_" + des + "_"
                    + des;
                paths.add(path);
                path_k.put(path,k);
                hub.add(i);
                hub.add(ii);
                hub.add(iii);
                hub.add(iiii);
                hub.add(des);
                path_candhubs.put(path, hub);
              }
            }
          }
        }
      }
    }

    //h2 is close
    if (l > 1) { //l=2
      for (int i : data.candhubs) {
        if (i != ori & i != des) {
          hub = new ArrayList<>();
          path = "p#" + ori + "_" + i + "_" + des;
          paths.add(path);
          path_k.put(path,k);
          hub.add(i);
          path_candhubs.put(path, hub);
        }
      }
    }
    if (l > 2) { //l=3
      for (int i : data.candhubs) {
        for (int ii : data.candhubs) {
          if (i != ori && i != des && i != ii && ii != ori && ii != des) {
            hub = new ArrayList<>();
            path = "p#" + ori + "_" + i + "_" + ii + "_" + des;
            paths.add(path);
            path_k.put(path,k);
            hub.add(i);
            hub.add(ii);
            path_candhubs.put(path, hub);
          }
        }
      }
    }
    if (l > 3) { //l=4
      for (int i : data.candhubs) {
        for (int ii : data.candhubs) {
          for (int iii : data.candhubs) {
            if (i != ori && i != des && i != ii && ii != ori && ii != des && iii != ori && iii != i
                && iii != ii && iii != des) {
              hub = new ArrayList<>();
              path = "p#" + ori + "_" + i + "_" + ii + "_" + iii + "_" + des;
              paths.add(path);
              path_k.put(path,k);
              hub.add(i);
              hub.add(ii);
              hub.add(iii);
              path_candhubs.put(path, hub);
            }
          }
        }
      }
    }
    if (l > 4) { //l=5
      for (int i : data.candhubs) {
        for (int ii : data.candhubs) {
          for (int iii : data.candhubs) {
            for (int iiii : data.candhubs) {
              if (i != ori && i != des && i != ii && ii != ori && ii != des && iii != ori
                  && iii != i && iii != ii && iii != des && iiii != ori && iiii != i && iiii != ii
                  && iiii != iii && iiii != des) {
                hub = new ArrayList<>();
                path = "p#" + ori + "_" + i + "_" + ii + "_" + iii + "_" + iiii + "_" + des;
                paths.add(path);
                path_k.put(path,k);
                hub.add(i);
                hub.add(ii);
                hub.add(iii);
                hub.add(iiii);
                path_candhubs.put(path, hub);
              }
            }
          }
        }
      }
    }

    k_paths.put(k, paths);

  }

  void CreatePathsHH(int k, int l, int ori, int des, HashMap<Integer, ArrayList<String>> k_paths,
      HashMap<String, ArrayList<Integer>> path_candhubs, ArrayList<String> paths) {
    String path;
    ArrayList<Integer> hub;

    // h1 and h2 are open
    hub = new ArrayList<>();
    path = "p#" + ori + "_" + ori + "_" + des + "_" + des;
    paths.add(path);
    path_k.put(path,k);
    hub.add(ori);
    hub.add(des);
    path_candhubs.put(path, hub);
    if (l > 1) { //l=2
      for (int i : data.candhubs) {
        if (i != ori & i != des) {
          hub = new ArrayList<>();
          path = "p#" + ori + "_" + ori + "_" + i + "_" + des + "_" + des;
          paths.add(path);
          path_k.put(path,k);
          hub.add(ori);
          hub.add(i);
          hub.add(des);
          path_candhubs.put(path, hub);
        }
      }
    }
    if (l > 2) { //l=3
      for (int i : data.candhubs) {
        for (int ii : data.candhubs) {
          if (i != ori && i != des && i != ii && ii != ori && ii != des) {
            hub = new ArrayList<>();
            path = "p#" + ori + "_" + ori + "_" + i + "_" + ii + "_" + des + "_" + des;
            paths.add(path);
            path_k.put(path,k);
            hub.add(ori);
            hub.add(i);
            hub.add(ii);
            hub.add(des);
            path_candhubs.put(path, hub);
          }
        }
      }
    }
    if (l > 3) { //l=4
      for (int i : data.candhubs) {
        for (int ii : data.candhubs) {
          for (int iii : data.candhubs) {
            if (i != ori && i != des && i != ii && ii != ori && ii != des && iii != ori && iii != i
                && iii != ii && iii != des) {
              hub = new ArrayList<>();
              path =
                  "p#" + ori + "_" + ori + "_" + i + "_" + ii + "_" + iii + "_" + des + "_" + des;
              paths.add(path);
              path_k.put(path,k);
              hub.add(ori);
              hub.add(i);
              hub.add(ii);
              hub.add(iii);
              hub.add(des);
              path_candhubs.put(path, hub);
            }
          }
        }
      }
    }
    if (l > 4) { //l=5
      for (int i : data.candhubs) {
        for (int ii : data.candhubs) {
          for (int iii : data.candhubs) {
            for (int iiii : data.candhubs) {
              if (i != ori && i != des && i != ii && ii != ori && ii != des && iii != ori
                  && iii != i && iii != ii && iii != des && iiii != ori && iiii != i && iiii != ii
                  && iiii != iii && iiii != des) {
                hub = new ArrayList<>();
                path =
                    "p#" + ori + "_" + ori + "_" + i + "_" + ii + "_" + iii + "_" + iiii + "_" + des
                        + "_" + des;
                paths.add(path);
                path_k.put(path,k);
                hub.add(ori);
                hub.add(i);
                hub.add(ii);
                hub.add(iii);
                hub.add(iiii);
                hub.add(des);
                path_candhubs.put(path, hub);
              }
            }
          }
        }
      }
    }

    //h1 is open and h2 is close
    hub = new ArrayList<>();
    path = "p#" + ori + "_" + ori + "_" + des;
    paths.add(path);
    path_k.put(path,k);
    hub.add(ori);
    path_candhubs.put(path, hub);
    if (l > 1) { //l=2
      for (int i : data.candhubs) {
        if (i != ori & i != des) {
          hub = new ArrayList<>();
          path = "p#" + ori + "_" + ori + "_" + i + "_" + des;
          paths.add(path);
          path_k.put(path,k);
          hub.add(ori);
          hub.add(i);
          path_candhubs.put(path, hub);
        }
      }
    }
    if (l > 2) { //l=3
      for (int i : data.candhubs) {
        for (int ii : data.candhubs) {
          if (i != ori && i != des && i != ii && ii != ori && ii != des) {
            hub = new ArrayList<>();
            path = "p#" + ori + "_" + ori + "_" + i + "_" + ii + "_" + des;
            paths.add(path);
            path_k.put(path,k);
            hub.add(ori);
            hub.add(i);
            hub.add(ii);
            path_candhubs.put(path, hub);
          }
        }
      }
    }
    if (l > 3) { //l=4
      for (int i : data.candhubs) {
        for (int ii : data.candhubs) {
          for (int iii : data.candhubs) {
            if (i != ori && i != des && i != ii && ii != ori && ii != des && iii != ori && iii != i
                && iii != ii && iii != des) {
              hub = new ArrayList<>();
              path = "p#" + ori + "_" + ori + "_" + i + "_" + ii + "_" + iii + "_" + des;
              paths.add(path);
              path_k.put(path,k);
              hub.add(ori);
              hub.add(i);
              hub.add(ii);
              hub.add(iii);
              path_candhubs.put(path, hub);
            }
          }
        }
      }
    }
    if (l > 4) { //l=5
      for (int i : data.candhubs) {
        for (int ii : data.candhubs) {
          for (int iii : data.candhubs) {
            for (int iiii : data.candhubs) {
              if (i != ori && i != des && i != ii && ii != ori && ii != des && iii != ori
                  && iii != i && iii != ii && iii != des && iiii != ori && iiii != i && iiii != ii
                  && iiii != iii && iiii != des) {
                hub = new ArrayList<>();
                path = "p#" + ori + "_" + ori + "_" + i + "_" + ii + "_" + iii + "_" + iiii + "_"
                    + des;
                paths.add(path);
                path_k.put(path,k);
                hub.add(ori);
                hub.add(i);
                hub.add(ii);
                hub.add(iii);
                hub.add(iiii);
                path_candhubs.put(path, hub);
              }
            }
          }
        }
      }
    }

    // h1 is close and h2 is open
    hub = new ArrayList<>();
    path = "p#" + ori + "_" + des + "_" + des;
    paths.add(path);
    path_k.put(path,k);
    hub.add(des);
    path_candhubs.put(path, hub);
    if (l > 1) { //l=2
      for (int i : data.candhubs) {
        if (i != ori & i != des) {
          hub = new ArrayList<>();
          path = "p#" + ori + "_" + i + "_" + des + "_" + des;
          paths.add(path);
          path_k.put(path,k);
          hub.add(i);
          hub.add(des);
          path_candhubs.put(path, hub);
        }
      }
    }
    if (l > 2) { //l=3
      for (int i : data.candhubs) {
        for (int ii : data.candhubs) {
          if (i != ori && i != des && i != ii && ii != ori && ii != des) {
            hub = new ArrayList<>();
            path = "p#" + ori + "_" + i + "_" + ii + "_" + des + "_" + des;
            paths.add(path);
            path_k.put(path,k);
            hub.add(i);
            hub.add(ii);
            hub.add(des);
            path_candhubs.put(path, hub);
          }
        }
      }
    }
    if (l > 3) { //l=4
      for (int i : data.candhubs) {
        for (int ii : data.candhubs) {
          for (int iii : data.candhubs) {
            if (i != ori && i != des && i != ii && ii != ori && ii != des && iii != ori && iii != i
                && iii != ii && iii != des) {
              hub = new ArrayList<>();
              path = "p#" + ori + "_" + i + "_" + ii + "_" + iii + "_" + des + "_" + des;
              paths.add(path);
              path_k.put(path,k);
              hub.add(i);
              hub.add(ii);
              hub.add(iii);
              hub.add(des);
              path_candhubs.put(path, hub);
            }
          }
        }
      }
    }
    if (l > 4) { //l=5
      for (int i : data.candhubs) {
        for (int ii : data.candhubs) {
          for (int iii : data.candhubs) {
            for (int iiii : data.candhubs) {
              if (i != ori && i != des && i != ii && ii != ori && ii != des && iii != ori
                  && iii != i && iii != ii && iii != des && iiii != ori && iiii != i && iiii != ii
                  && iiii != iii && iiii != des) {
                hub = new ArrayList<>();
                path = "p#" + ori + "_" + i + "_" + ii + "_" + iii + "_" + iiii + "_" + des + "_"
                    + des;
                paths.add(path);
                path_k.put(path,k);
                hub.add(i);
                hub.add(ii);
                hub.add(iii);
                hub.add(iiii);
                hub.add(des);
                path_candhubs.put(path, hub);
              }
            }
          }
        }
      }
    }

    // h1 and h2 are close
    if (l > 1) { //l=2
      for (int i : data.candhubs) {
        if (i != ori & i != des) {
          hub = new ArrayList<>();
          path = "p#" + ori + "_" + i + "_" + des;
          paths.add(path);
          path_k.put(path,k);
          hub.add(i);
          path_candhubs.put(path, hub);
        }
      }
    }
    if (l > 2) { //l=3
      for (int i : data.candhubs) {
        for (int ii : data.candhubs) {
          if (i != ori && i != des && i != ii && ii != ori && ii != des) {
            hub = new ArrayList<>();
            path = "p#" + ori + "_" + i + "_" + ii + "_" + des;
            paths.add(path);
            path_k.put(path,k);
            hub.add(i);
            hub.add(ii);
            path_candhubs.put(path, hub);
          }
        }
      }
    }
    if (l > 3) { //l=4
      for (int i : data.candhubs) {
        for (int ii : data.candhubs) {
          for (int iii : data.candhubs) {
            if (i != ori && i != des && i != ii && ii != ori && ii != des && iii != ori && iii != i
                && iii != ii && iii != des) {
              hub = new ArrayList<>();
              path = "p#" + ori + "_" + i + "_" + ii + "_" + iii + "_" + des;
              paths.add(path);
              path_k.put(path,k);
              hub.add(i);
              hub.add(ii);
              hub.add(iii);
              path_candhubs.put(path, hub);
            }
          }
        }
      }
    }
    if (l > 4) { //l=5
      for (int i : data.candhubs) {
        for (int ii : data.candhubs) {
          for (int iii : data.candhubs) {
            for (int iiii : data.candhubs) {
              if (i != ori && i != des && i != ii && ii != ori && ii != des && iii != ori
                  && iii != i && iii != ii && iii != des && iiii != ori && iiii != i && iiii != ii
                  && iiii != iii && iiii != des) {
                hub = new ArrayList<>();
                path = "p#" + ori + "_" + i + "_" + ii + "_" + iii + "_" + iiii + "_" + des;
                paths.add(path);
                path_k.put(path,k);
                hub.add(i);
                hub.add(ii);
                hub.add(iii);
                hub.add(iiii);
                path_candhubs.put(path, hub);
              }
            }
          }
        }
      }
    }

    k_paths.put(k, paths);
  }

  void findpathcosts() {
    path_cost = new HashMap<>();
    double cost;
    int h_count;
    for (int k = 0; k < data.num_od; k++) {
      for (String p : k_paths.get(k)) {
        h_count = path_candhubs.get(p).size();
        cost = 0;
        cost = cost + data.Collection_Coeff * data.C[t][data.k_od.get(k)[0]][path_candhubs.get(p)
            .get(0)];
        if (h_count > 1) {
          for (int i = 0; i < h_count - 1; i++) {
            cost = cost + data.alpha * data.C[t][path_candhubs.get(p).get(i)][path_candhubs.get(p)
                .get(i + 1)];
          }
        }
        cost = cost + data.Distribution_Coeff * data.C[t][path_candhubs.get(p)
            .get(h_count - 1)][data.k_od.get(k)[1]];
        if (cost > data.bigM) {
          InfeasiblePaths.add(p);
        }
        cost = cost * data.W[t][sc][k];
        //cost=data.bigM;
        path_cost.put(p, cost);
      }
    }
  }

  void findpathtimes() {
        //Finding Path Times
        path_time = new HashMap<>();

        int h_count;
        for (int k = 0; k < data.num_od; k++) {
            for (String p : k_paths.get(k)) {
                h_count = path_candhubs.get(p).size();
                double time = 0;
                time = time + data.time[t][data.k_od.get(k)[0]][path_candhubs.get(p).get(0)];
                if (h_count > 1) {
                    for (int i = 0; i < h_count - 1; i++) {
                        time = time + data.time[t][path_candhubs.get(p).get(i)][path_candhubs.get(p).get(i + 1)];
                    }
                }
                time = time + data.time[t][path_candhubs.get(p).get(h_count - 1)][data.k_od.get(k)[1]];
                path_time.put(p, time);
            }
        }
    }

}