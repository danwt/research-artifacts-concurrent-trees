package util;

import com.fasterxml.jackson.databind.ObjectMapper;
import tlc2.overrides.StandardAvlTreeGeneration;

import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

public class JsonGraph {

    private static class Edge {
        Integer src;
        Integer dst;
        boolean left;

        public Integer getSrc() {
            return src;
        }

        public Integer getDst() {
            return dst;
        }

        public boolean getLeft() {
            return left;
        }
    }

    private static void addEdges(List<Edge> list, StandardAvlTreeGeneration.Node n) {
        if (n == null) {
            return;
        }
        if (n.left != null) {
            Edge e = new Edge();
            e.src = n.k;
            e.dst = n.left.k;
            e.left = Boolean.valueOf(true);
            list.add(e);
        }
        if (n.rite != null) {
            Edge e = new Edge();
            e.src = n.k;
            e.dst = n.rite.k;
            e.left = Boolean.valueOf(false);
            list.add(e);
        }
        addEdges(list, n.left);
        addEdges(list, n.rite);
    }

    private static List<Edge> edgeList(StandardAvlTreeGeneration.Node n) {
        List<Edge> ret = new ArrayList<>();
        addEdges(ret, n);
        return ret;
    }

    public static boolean writeJson(List<StandardAvlTreeGeneration.Node> logicalTrees,
                                    String path) {
        boolean succeed = true;
        ObjectMapper mapper = new ObjectMapper();
        List<List<Edge>> trees =
                logicalTrees.stream().map(it -> JsonGraph.edgeList(it)).collect(Collectors.toList());
        try {
            mapper.writeValue(Paths.get(path).toFile(), trees);
        } catch (Exception e) {
            System.out.println("Exception caught: " + e.getMessage());
            succeed = false;
        }
        return succeed;
    }

}
