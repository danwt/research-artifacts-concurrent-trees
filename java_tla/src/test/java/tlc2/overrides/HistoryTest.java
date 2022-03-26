package tlc2.overrides;

import org.junit.Test;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import static org.junit.Assert.*;

public class HistoryTest  {

    @Test
    public void historyTestSmoke(){
        assertTrue(true);
    }

    History linearizableHistory1(){

        History h = new History();

        h.addInvocationWithNextId("p0", History.OperationType.INSERT,"1"); // Id 0
        h.addResponse("p0",true);
        h.addInvocationWithNextId("p1", History.OperationType.GET,"1"); // Id 1
        h.addInvocationWithNextId("p2", History.OperationType.INSERT,"1"); // Id 2
        h.addInvocationWithNextId("p0", History.OperationType.ERASE,"1"); // Id 3
        h.addResponse("p1",true);
        h.addResponse("p0",true);
        h.addResponse("p2",false);
        h.addInvocationWithNextId("p1", History.OperationType.ERASE,"1"); // Id 4
        h.addResponse("p1",false);

        return h;
    }

    History nonLinearizableHistory1(){

        History h = new History();

        h.addInvocationWithNextId("p0", History.OperationType.ERASE,"1"); // Id 0
        h.addInvocationWithNextId("p1", History.OperationType.INSERT,"1"); // Id 1
        h.addResponse("p0", true);
        h.addInvocationWithNextId("p0", History.OperationType.GET,"1"); // Id 2
        h.addResponse("p0", true);
        h.addResponse("p1", true);

        return h;
    }


    @Test
    public void opensClosedSizes(){

        History h = linearizableHistory1();

        assertTrue(h.openSet.isEmpty());
        assertEquals(h.closedSet.size(),5);

    }

    @Test
    public void sequentialHistoryHasCorrectOrdering(){

        History h = new History();

        h.addInvocation("p0", History.OperationType.INSERT, "1", 0);
        h.addResponse("p0", true);
        h.addInvocation("p1", History.OperationType.GET, "1", 1);
        h.addResponse("p1", true);
        h.addInvocation("p2", History.OperationType.ERASE, "1", 2);
        h.addResponse("p2", true);
        h.addInvocation("p0", History.OperationType.ERASE, "1", 3);
        h.addResponse("p0", false);
        h.addInvocation("p1", History.OperationType.INSERT, "1", 4);
        h.addResponse("p1", true);
        h.addInvocation("p2", History.OperationType.INSERT, "1", 5);
        h.addResponse("p2", false);

        Set<Integer> allOps = new HashSet<Integer>(){{
            add(0);
            add(1);
            add(2);
            add(3);
            add(4);
            add(5);
        }};

        for(Integer id:allOps){
            Set<Integer> happensBefore = h.happensBefore.get(id);
            Set<Integer> happensAfter = h.happensAfter.get(id);

            assertFalse(happensBefore.contains(id));
            assertFalse(happensAfter.contains(id));
            assertTrue(Collections.disjoint(happensBefore,happensAfter));

            Set<Integer> union = new HashSet<>(happensBefore);
            union.addAll(happensAfter);
            union.add(id);
            assertTrue(union.equals(allOps));
        }

    }

    @Test
    public void happensBefore(){
        History h = linearizableHistory1();
        assertEquals(h.happensBefore.get(h.operations.get(0).id),new HashSet<Integer>(){{
        }});

        assertEquals(h.happensBefore.get(h.operations.get(1).id),new HashSet<Integer>(){{
            add(0);
        }});

        assertEquals(h.happensBefore.get(h.operations.get(2).id),new HashSet<Integer>(){{
            add(0);
        }});

        assertEquals(h.happensBefore.get(h.operations.get(3).id),new HashSet<Integer>(){{
            add(0);
        }});

        assertEquals(h.happensBefore.get(h.operations.get(4).id),new HashSet<Integer>(){{
            add(0);
            add(1);
            add(2);
            add(3);
        }});
    }

    @Test
    public void happensAfter(){
        History h = linearizableHistory1();
        assertEquals(h.happensAfter.get(h.operations.get(0).id),new HashSet<Integer>(){{
            add(1);
            add(2);
            add(3);
            add(4);
        }});

        assertEquals(h.happensAfter.get(h.operations.get(1).id),new HashSet<Integer>(){{
            add(4);
        }});

        assertEquals(h.happensAfter.get(h.operations.get(2).id),new HashSet<Integer>(){{
            add(4);
        }});

        assertEquals(h.happensAfter.get(h.operations.get(3).id),new HashSet<Integer>(){{
            add(4);
        }});

        assertEquals(h.happensAfter.get(h.operations.get(4).id),new HashSet<Integer>(){{
        }});
    }

    @Test
    public void isLinearizableTrue(){
        History h = linearizableHistory1();
        boolean isLinearizable = h.isLinearizable( new HashSet<Integer>() );
        assertTrue(isLinearizable);
    }

    @Test
    public void isLinearizableFalse(){
        History h = nonLinearizableHistory1();
        boolean isLinearizable = h.isLinearizable( new HashSet<Integer>() );
        assertFalse(isLinearizable);
    }

}