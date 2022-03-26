package util;

import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.AllArgsConstructor;
import lombok.Data;

import java.nio.file.Paths;
import java.util.List;

public class JsonGraph {

    @Data
    @AllArgsConstructor
    public static class Node {
        int id;
        String key;
        String value;
        boolean isChunkRoot;
        boolean isLeaf;
        int heightField;
    }

    @Data
    @AllArgsConstructor
    public static class Edge {
        Node src;
        Node dst;
        String type; // parent, left, rite
    }

    public static boolean writeJson(List<Edge> edgeList,
                                    String path) {
        boolean succeed = true;
        ObjectMapper mapper = new ObjectMapper();
        try {
            mapper.writeValue(Paths.get(path).toFile(), edgeList);
        } catch (Exception e) {
            System.out.println("Exception caught: " + e.getMessage());
            succeed = false;
        }
        return succeed;
    }

}
