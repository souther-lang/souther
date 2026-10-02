package souther.compiler;

import com.sun.management.ThreadMXBean;
import org.junit.jupiter.api.Test;

import java.lang.management.ManagementFactory;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A chain of records, each holding the one before and each with a rule of its own, reads at each
 * record the rule of every record under it, at a projection as deep as that record is under it. So
 * the chain is read in the square of its length and no faster; what this holds is that it is read in
 * no more than that — that a rule costs what it says and not how deep it was read.
 *
 * <p>Held over a doubling, as what compiling the chain allocates on the thread that compiles it.
 * Every reading that walked a projection at each rule — the names written out, a place copied, a
 * table of positions copied for one more, an origin a layer per name — allocated as it walked, and
 * what is allocated is the same each run whatever else the machine is doing, which the time is not.
 * One compile first, so what the first one makes of the compiler itself is not counted against the
 * shorter chain.
 */
class AChainOfRecordsEachWithARuleCompilesInTheSquareOfItsLengthTest {

    private static String chain(int records) {
        StringBuilder src = new StringBuilder("module chain\n\n");
        for (int i = 1; i <= records; i++) {
            src.append("data T").append(i).append(" = { ");
            if (i > 1) {
                src.append("p: T").append(i - 1).append(", ");
            }
            src.append("k: Int }\n    invariant k").append(i).append(" = k >= ").append(i)
                    .append('\n');
        }
        return src.toString();
    }

    private static long allocatedCompiling(int records) {
        ThreadMXBean thread = (ThreadMXBean) ManagementFactory.getThreadMXBean();
        String src = chain(records);
        long before = thread.getCurrentThreadAllocatedBytes();
        Compiler.compile(src);
        return thread.getCurrentThreadAllocatedBytes() - before;
    }

    @Test
    void doublingTheChainAboutQuadruplesWhatCompilingItAllocates() {
        allocatedCompiling(40);
        long shorter = allocatedCompiling(80);
        long longer = allocatedCompiling(160);
        assertTrue(longer * 10 <= shorter * 42,
                "80 records allocated " + shorter + " bytes and 160 allocated " + longer);
    }
}
