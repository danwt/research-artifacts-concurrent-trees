package tlc2.overrides;

import org.junit.Ignore;
import org.junit.Test;
import util.JsonGraph;

import static org.junit.Assert.assertTrue;

public class PrintJsonTrees {

    @Test
    @Ignore
    public void dumpJsonForSomeInterestingAvlTrees() {
        boolean success = JsonGraph.writeJson(
                StandardAvlTreeGeneration.generateAllInterestingAvlTrees(2,10,8,8),
                "../../visualize/src/json/java_generated_avls.json");
        assertTrue(success);
    }
}
