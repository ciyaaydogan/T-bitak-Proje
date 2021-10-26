import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;

public class Data {

  Boolean print = false;
  double bigM = 1e4;
  Boolean CompleteNetwork = true;
  double cong_up = 0.90;
  double CongCoef = (1 / cong_up);
  double T_up = 1.5;
  double delta_z = 0.1;
  double baseusagerate = 0.5;
  double expHubTime;
  double inflation = 0.05;

  ArrayList<Integer>[] I;
  int[] a;
  double[][] pr;
  double W_up = 0.1;
  double W_down = -0.05;
  int maxnumsce;

  double[][][] node_totalInflow;
  double[][][] node_totaloutflow;
  double[][][] sigma_outflow;
  double[][][] sigma_inflow;
  double[][][] sigma_n;
  double[][] sigma;

  //file
  String outputDir;
  String resultsFileName;
  int nHubs;
  int nNodes;
  ArrayList<Integer> candhubs;
  double[][] F; // fixed cost
  double[] Q; // Max capacity
  double[][] K;
  double[][][] W; // flows
  double[][][][] WW; // flows
  double[][][] C;  // distance - cost
  double[][][] time; // time of arcs
  double[][] Tmin; // min time for k
  double F_a = inflation; //artış oranı
  double C_a = inflation; //artış oranı
  double T_a = 0; //artış oranı
  double[][] A;
  double[][] B;
  int nPeriod;
  //parameters
  double Collection_Coeff;
  double alpha; //Transfer_Coeff
  double Distribution_Coeff;
  double[] g; //Cap_Unit_Cost
  double g_a = 0.05;
  double b;
  double Weight_Coeff;
  int Path_Length_Limit;
  int Num_Cap_Levels;
  int Num_Init_Paths;
  int Num_Threads;
  double Time_Limit;
  int num_od;
  double[][] totalflow;
  double[][][] HminCap;
  double[] interHubs;
  HashMap<Integer, int[]> k_od;
  boolean cpx_true_labeling_false = false;
  String datafp;
  String paramfp;

  Data(String dataFilePath, String paramsFilePath, String resultsFileName) throws IOException {
    datafp = dataFilePath.substring(5, dataFilePath.length() - 4);
    paramfp = paramsFilePath.substring(5, paramsFilePath.length() - 4);

    readData(dataFilePath, paramsFilePath);

    this.outputDir = outputDir;
    this.resultsFileName = resultsFileName;
    //  name = getFileName(dataFilePath);

    //printInfo();
  }

  void readData(String dataFilePath, String paramsFilePath) throws IOException {
    FileReader fi = new FileReader(dataFilePath);
    BufferedReader br = new BufferedReader(fi);
    String line = br.readLine();
    String[] words = Arrays.stream(line.split("\\s+")).filter(s -> !s.isEmpty())
        .toArray(String[]::new);
    nNodes = Integer.parseInt(words[0]);
    nHubs = Integer.parseInt(words[1]);
    line = br.readLine();
    nPeriod = Integer.parseInt(line);
    candhubs = new ArrayList<>();
    F = new double[nPeriod + 1][nNodes];
    Q = new double[nNodes];
    W = new double[nPeriod + 1][(int) (Math.pow(2, nPeriod - 1) + 1)][nNodes * (nNodes - 1)];
    WW = new double[nPeriod + 1][(int) (Math.pow(2, nPeriod - 1) + 1)][nNodes][nNodes];
    C = new double[nPeriod + 1][nNodes][nNodes];
    time = new double[nPeriod + 1][nNodes][nNodes];
    num_od = nNodes * (nNodes - 1);
    System.out.println(nNodes + "----" + nHubs);
    for (int i = 0; i < nHubs; i++) {
      line = br.readLine();
      candhubs.add(Integer.parseInt(line));
      //System.out.println(hubs[i]);
      System.out.println(candhubs.get(i));
    }
    br.readLine();
    for (int i = 0; i < nHubs; i++) {
      line = br.readLine();
      words = Arrays.stream(line.split("\\s+")).filter(s -> !s.isEmpty()).toArray(String[]::new);
      F[1][candhubs.get(i)] = Double.parseDouble(words[0]);
      for (int t = 1; t < nPeriod; t++) {
        F[t + 1][candhubs.get(i)] = F[t + 1][candhubs.get(i)] * (1 + F_a);
      }
      Q[candhubs.get(i)] = Double.parseDouble(words[1]);
    }

    for (int i = 0; i < nNodes; i++) {
      if (F[1][i] > 0) {
        System.out.println("F(1," + (i + 1) + "):" + F[1][i]);
        System.out.println("Q(1," + (i + 1) + "):" + Q[i]);
      }
    }
    br.readLine();
    k_od = new HashMap<>();
    maxnumsce = (int) (Math.pow(2, nPeriod - 1) + 1);
    totalflow = new double[nPeriod + 1][maxnumsce];
    HminCap = new double[nPeriod + 1][maxnumsce][nNodes];
    interHubs = new double[nPeriod + 1];

    I = new ArrayList[nPeriod + 1];
    I[0] = new ArrayList<>();
    I[1] = new ArrayList<>();
    I[2] = new ArrayList<>();
    I[3] = new ArrayList<>();
    I[0].add(1);
    I[1].add(1);
    I[2].add(1);
    I[2].add(2);
    I[3].add(1);
    I[3].add(2);
    I[3].add(3);
    I[3].add(4);
    a = new int[maxnumsce];
    a[1] = 1;
    a[2] = 1;
    a[3] = 2;
    a[4] = 2;

    pr = new double[nPeriod + 1][maxnumsce];
    pr[1][1] = 1;
    pr[2][1] = 0.5;
    pr[2][2] = 0.5;
    pr[3][1] = 0.25;
    pr[3][2] = 0.25;
    pr[3][3] = 0.25;
    pr[3][4] = 0.25;

    for (int k = 0; k < (nNodes * (nNodes - 1)); k++) {
      line = br.readLine();
      words = Arrays.stream(line.split("\\s+")).filter(s -> !s.isEmpty()).toArray(String[]::new);
      int i = Integer.parseInt(words[0]);
      int j = Integer.parseInt(words[1]);
      C[1][i][j] = Double.parseDouble(words[2]);
      if (C[1][i][j] == -1) {
        CompleteNetwork = false;
        C[1][i][j] = bigM;
        for (int t = 1; t < nPeriod; t++) {
          C[t + 1][i][j] = bigM;
        }
      } else {
        for (int t = 1; t < nPeriod; t++) {
          C[t + 1][i][j] = C[t][i][j] * (1 + C_a);
        }
      }

      W[1][1][k] = Double.parseDouble(words[3]);
      WW[1][1][i][j] = Double.parseDouble(words[3]);
      W[2][1][k] = W[1][1][k] * (1 + W_up);
      WW[2][1][i][j] = WW[1][1][i][j] * (1 + W_up);
      W[2][2][k] = W[1][1][k] * (1 + W_down);
      WW[2][2][i][j] = WW[1][1][i][j] * (1 + W_down);
      W[3][1][k] = W[2][1][k] * (1 + W_up);
      WW[3][1][i][j] = WW[2][1][i][j] * (1 + W_up);
      W[3][2][k] = W[2][1][k] * (1 + W_down);
      WW[3][2][i][j] = WW[2][1][i][j] * (1 + W_down);
      W[3][3][k] = W[2][2][k] * (1 + W_up);
      WW[3][3][i][j] = WW[2][2][i][j] * (1 + W_up);
      W[3][4][k] = W[2][2][k] * (1 + W_down);
      WW[3][4][i][j] = WW[2][2][i][j] * (1 + W_down);
      time[1][i][j] = Double.parseDouble(words[4]);

      if (time[1][i][j] == 0) {
        time[1][i][j] = C[1][i][j];
      }
      for (int t = 1; t < nPeriod; t++) {
        time[t + 1][i][j] = time[t][i][j] * (1 + T_a);
      }
      int[] o_d = new int[2];
      o_d[0] = i;
      o_d[1] = j;
      k_od.put(k, o_d);
    }

    A = new double[nPeriod + 1][nNodes];
    B = new double[nPeriod + 1][nNodes];
    for (int t = 1; t <= nPeriod; t++) {
      for (int h : candhubs) {
        A[t][h] = F[t][h];
        B[t][h] = -0.2 * F[t][h];
      }
    }
    for (int t = 1; t <= nPeriod; t++) {
      for (int sc : I[t]) {
        System.out.println("TotalFlow_t(" + t + ")_sc(" + sc + "): " + totalflow[t][sc]);
      }
    }

    FileReader fil = new FileReader(paramsFilePath);
    br = new BufferedReader(fil);

    line = br.readLine();
    words = Arrays.stream(line.split("\\s+")).filter(s -> !s.isEmpty()).toArray(String[]::new);
    Collection_Coeff = Double.parseDouble(words[1]);

    line = br.readLine();
    words = Arrays.stream(line.split("\\s+")).filter(s -> !s.isEmpty()).toArray(String[]::new);
    alpha = Double.parseDouble(words[1]);

    line = br.readLine();
    words = Arrays.stream(line.split("\\s+")).filter(s -> !s.isEmpty()).toArray(String[]::new);
    Distribution_Coeff = Double.parseDouble(words[1]);

    g = new double[nPeriod + 1];
    line = br.readLine();
    words = Arrays.stream(line.split("\\s+")).filter(s -> !s.isEmpty()).toArray(String[]::new);
    g[1] = Double.parseDouble(words[1]);
    for (int t = 1; t < nPeriod; t++) {
      g[t + 1] = g[t] * (1 + g_a);
    }

    line = br.readLine();
    words = Arrays.stream(line.split("\\s+")).filter(s -> !s.isEmpty()).toArray(String[]::new);
    b = Double.parseDouble(words[1]);

    line = br.readLine();
    words = Arrays.stream(line.split("\\s+")).filter(s -> !s.isEmpty()).toArray(String[]::new);
    Weight_Coeff = Double.parseDouble(words[1]);

    line = br.readLine();
    words = Arrays.stream(line.split("\\s+")).filter(s -> !s.isEmpty()).toArray(String[]::new);
    Path_Length_Limit = Integer.parseInt(words[1]);

    line = br.readLine();
    words = Arrays.stream(line.split("\\s+")).filter(s -> !s.isEmpty()).toArray(String[]::new);
    Num_Cap_Levels = Integer.parseInt(words[1]);

    line = br.readLine();
    words = Arrays.stream(line.split("\\s+")).filter(s -> !s.isEmpty()).toArray(String[]::new);
    Num_Init_Paths = Integer.parseInt(words[1]);

    line = br.readLine();
    words = Arrays.stream(line.split("\\s+")).filter(s -> !s.isEmpty()).toArray(String[]::new);
    Num_Threads = Integer.parseInt(words[1]);

    line = br.readLine();
    words = Arrays.stream(line.split("\\s+")).filter(s -> !s.isEmpty()).toArray(String[]::new);
    Time_Limit = Double.parseDouble(words[1]);

    K = new double[nNodes][Num_Cap_Levels + 1];
    for (int h : candhubs) {
      for (int caplev = 1; caplev <= Num_Cap_Levels; caplev++) {
        K[h][caplev] = (Q[h] / Num_Cap_Levels) * caplev;
      }
    }

    line = br.readLine();
    words = Arrays.stream(line.split("\\s+")).filter(s -> !s.isEmpty()).toArray(String[]::new);
    T_up = Double.parseDouble(words[1]);

    line = br.readLine();
    words = Arrays.stream(line.split("\\s+")).filter(s -> !s.isEmpty()).toArray(String[]::new);
    delta_z = Double.parseDouble(words[1]);

    line = br.readLine();
    words = Arrays.stream(line.split("\\s+")).filter(s -> !s.isEmpty()).toArray(String[]::new);
    baseusagerate = Double.parseDouble(words[1]);
    expHubTime = (baseusagerate / (1 - baseusagerate));

    System.out.println("Time Limit: " + Time_Limit);
    System.out.println("T_up: " + T_up);
    System.out.println("delta_z: " + delta_z);
    System.out.println("baseusagerate: " + baseusagerate);

    Tmin = new double[nPeriod + 1][num_od];

    for (int k = 0; k < num_od; k++) {
      int ori = k_od.get(k)[0];
      int des = k_od.get(k)[1];
      Label L = new Label();
      L.n = ori;
      L.c = 0;
      L.l = Path_Length_Limit;
      L.N = new ArrayList<>(candhubs);
      L.hubs = new ArrayList();
      L.path = "p#" + ori;
      if (candhubs.contains(ori)) {
        L.path = L.path + "_" + ori;
        L.hubs.add(ori);
      }
      ArrayList<Label>[] Labels = new ArrayList[nNodes];
      for (int n : L.N) {
        Labels[n] = new ArrayList<>();
        Label L_ = new Label();
        L_.n = n;
        L_.c = L.c + time[1][ori][n];
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
      ArrayList<Label>[] NewAdddedLabels = new ArrayList[nNodes];
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
                L_.c = lab.c + time[1][lab.n][n_];
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
          lab.c = lab.c + time[1][lab.n][des];
          lab.path = lab.path + "_" + des;
          if (candhubs.contains(des)) {
            lab.path = lab.path + "_" + des;
            lab.hubs.add(des);
          }
          if (T_min > lab.c) {
            T_min = lab.c;
          }
        }
      }
      Tmin[1][k] = T_min * T_up;
      for (int t = 1; t < nPeriod; t++) {
        Tmin[t + 1][k] = Tmin[t][k] * (1 + T_a);
      }
      for (int t = 1; t <= nPeriod; t++) {
        Tmin[t][k] = Tmin[t][k] + expHubTime;
      }
    }

    for (int t = 1; t <= nPeriod; t++) {
      for (int sc : I[t]) {
        for (int k = 0; k < W[t][sc].length; k++) {
          W[1][1][k] = W[1][1][k] * Weight_Coeff;
        }
        for (int i = 0; i < WW[t][sc].length; i++) {
          for (int j = 0; j < WW[t][sc][i].length; j++) {
            WW[t][sc][i][j] = WW[t][sc][i][j] * Weight_Coeff;
          }
        }
      }
    }
    for (int k = 0; k < (nNodes * (nNodes - 1)); k++) {
      for (int t = 1; t <= nPeriod; t++) {
        for (int sc : I[t]) {
          totalflow[t][sc] = totalflow[t][sc] + W[t][sc][k];
        }
      }
      for (int t = 1; t <= nPeriod; t++) {
        for (int sc : I[t]) {
          if (candhubs.contains(k_od.get(k)[0])) {
            HminCap[t][sc][k_od.get(k)[0]] = HminCap[t][sc][k_od.get(k)[0]] + W[t][sc][k];
          }
          if (candhubs.contains(k_od.get(k)[1])) {
            HminCap[t][sc][k_od.get(k)[1]] = HminCap[t][sc][k_od.get(k)[1]] + W[t][sc][k];
          }
        }
      }
    }
    node_totalInflow = new double[nPeriod + 1][(int) (Math.pow(2, nPeriod - 1) + 1)][nNodes];
    node_totaloutflow = new double[nPeriod + 1][(int) (Math.pow(2, nPeriod - 1) + 1)][nNodes];
    sigma_inflow = new double[nPeriod + 1][(int) (Math.pow(2, nPeriod - 1) + 1)][nNodes];
    sigma_outflow = new double[nPeriod + 1][(int) (Math.pow(2, nPeriod - 1) + 1)][nNodes];
    sigma_n = new double[nPeriod + 1][(int) (Math.pow(2, nPeriod - 1) + 1)][nNodes];
    sigma = new double[nPeriod + 1][(int) (Math.pow(2, nPeriod - 1) + 1)];
    for (int t = 1; t <= nPeriod; t++) {
      for (int sc : I[t]) {
        for (int i = 0; i < nNodes; i++) {
          for (int j = 0; j < nNodes; j++) {
            node_totaloutflow[t][sc][i] = node_totaloutflow[t][sc][i] + CongCoef * WW[t][sc][i][j];
            node_totalInflow[t][sc][i] = node_totalInflow[t][sc][i] + CongCoef * WW[t][sc][j][i];
          }
        }
      }
    }

    double[][][] totalcap_n_out = new double[nPeriod + 1][(int) (Math.pow(2, nPeriod - 1)
        + 1)][nNodes];
    double[][][] totalcap_n_in = new double[nPeriod + 1][(int) (Math.pow(2, nPeriod - 1)
        + 1)][nNodes];
    for (int t = 1; t <= nPeriod; t++) {
      for (int sc : I[t]) {
        for (int i = 0; i < nNodes; i++) {
          for (int h : candhubs) {
            if (C[t][i][h] != bigM) {
              totalcap_n_out[t][sc][i] = totalcap_n_out[t][sc][i] + Q[h];
            }
            if (C[t][h][i] != bigM) {
              totalcap_n_in[t][sc][i] = totalcap_n_in[t][sc][i] + Q[h];
            }
          }
        }
      }
    }

    for (int t = 1; t <= nPeriod; t++) {
      for (int sc : I[t]) {
        for (int i = 0; i < nNodes; i++) {
          sigma_inflow[t][sc][i] = node_totalInflow[t][sc][i] / totalcap_n_in[t][sc][i];
          sigma_outflow[t][sc][i] = node_totaloutflow[t][sc][i] / totalcap_n_in[t][sc][i];
          sigma_n[t][sc][i] = Math.max(sigma_inflow[t][sc][i], sigma_outflow[t][sc][i]);
        }
      }
    }

    for (int t = 1; t <= nPeriod; t++) {
      for (int sc : I[t]) {
        for (int i = 0; i < nNodes; i++) {
          if (sigma[t][sc] < sigma_n[t][sc][i]) {
            sigma[t][sc] = sigma_n[t][sc][i];
          }
        }
      }
    }

  }
}

