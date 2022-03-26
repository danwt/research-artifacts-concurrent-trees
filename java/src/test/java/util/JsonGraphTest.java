package util;

import org.junit.jupiter.api.Test;
import util.JsonGraph.*;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertTrue;

class JsonGraphTest {

    @Test
    public void simple() {

        List<Edge> edges = new ArrayList();

        edges.add(new Edge(
                new Node(0, "0", "0", true, true, 42),
                new Node(1, "1", "1", false, true, 42),
                "left"
        ));

        boolean succeed = JsonGraph.writeJson(edges, "/Users/danwt/documents/msc-papers/thesis-scratch-space/dump/jsongraphtest.json");
        assertTrue(succeed);

    }

}