import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;

public class Main {
    public static void main(String[] args) {
        System.out.println("--------------------");
        //String inputDir = "C:/Users/90543/IdeaProjects/in/MultiPeriod";
        String inputDir = "./in/";
        //String resultsFilePath = "C:/Users/90543/IdeaProjects/MPHLPCC_rmax_allpathslabeling/out/";
        String resultsFilePath = "./out/";
        if (args.length >= 1) {
            inputDir = args[0];
        }

        try (var inFiles = Files.list(Paths.get(inputDir)).filter(Files::isRegularFile).sorted().map(Path::toString)) {
            ArrayList<String> dataFiles = new ArrayList<String>();
            ArrayList<String> paramFiles = new ArrayList<String>();

            inFiles.forEach(f -> {
                if (f.endsWith(".dat")) {
                    dataFiles.add(f);
                } else if (f.endsWith(".par")) {
                    paramFiles.add(f);
                }
            });

            for (var df : dataFiles) {
                for (var pf : paramFiles) {
                    run(df, pf, resultsFilePath);
                }
            }
        } catch (Exception e) {
            System.err.println("Error: " + e.getMessage());
            e.printStackTrace();
        }
    }

    static void run(String dataFilePath, String paramsFilePath, String resultsFilePath) throws Exception {
        System.out.println("Parametre: " + dataFilePath);
        System.out.println("Data: " +paramsFilePath );
        double StartTime = System.currentTimeMillis();
        Data data = new Data(dataFilePath, paramsFilePath, resultsFilePath);
        System.out.println("Parametre: " + dataFilePath);
        System.out.println("Data: " +paramsFilePath );
        MasterProblem mp = new MasterProblem(data, dataFilePath, paramsFilePath, StartTime, resultsFilePath);
        double FinishTime = System.currentTimeMillis();
        double Time = (FinishTime - StartTime) / 1000;
        System.out.println("Total Time: " + Time);
    }

}