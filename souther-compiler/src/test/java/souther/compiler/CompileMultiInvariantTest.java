package souther.compiler;

import souther.runtime.ConstraintViolation;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A data may state more than one {@code invariant} line; every one must hold. Earlier only the
 * last survived (each line overwrote the previous), so a value breaking an earlier one was minted
 * anyway. All lines are now conjoined, so any single violation aborts (spec §invariant, §jvm-abort).
 */
class CompileMultiInvariantTest {

    private static final String MODULE = """
            module demo

            data In = Int
            data Amount = Int
                invariant value > 0
                invariant value < 100

            behavior make : (i: In) -> Amount constructs Amount
            let make (i) = Amount { value = i.value }
            """;

    private static Object make(long v, BytesClassLoader loader) throws Exception {
        Object in = Codecs.decoded(loader, "demo.In", v);
        Object make = Emitted.behavior(loader, "demo", "make").getConstructor().newInstance();
        return Codecs.apply(make, in);
    }

    @Test
    void aValueInBothBoundsIsMinted() throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(MODULE), CompileMultiInvariantTest.class.getClassLoader());
        Object amount = make(50L, loader);
        assertEquals(50L, Codecs.encode(loader, "demo.Amount", amount));
    }

    @Test
    void breakingTheFirstInvariantAborts() throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(MODULE), CompileMultiInvariantTest.class.getClassLoader());
        // value > 0 is the first line; only the last (value < 100) used to be enforced
        assertThrows(ConstraintViolation.class, () -> make(0L, loader));
    }

    @Test
    void breakingTheLastInvariantAborts() throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(MODULE), CompileMultiInvariantTest.class.getClassLoader());
        assertThrows(ConstraintViolation.class, () -> make(150L, loader));
    }

    /**
     * An invariant reads the fields a spread brought in as its own, including through a spread of a
     * spread. They are named where the invariant is written, so name resolution has to reach them
     * the same way the check does.
     */
    @Test
    void anInvariantReadsTheFieldsASpreadBringsIn() {
        String src = """
                module demo

                data Common = { createdOn: Int }
                data Worked = { ...Common, touches: Int }
                data Lead = { ...Worked, score: Int }
                    invariant touches >= 1 && createdOn >= 0 && score >= 0

                behavior make : (n: Int) -> Lead constructs Lead
                let make (n) = Lead { createdOn = n, touches = 1, score = n }
                """;

        assertEquals(true, Compiler.compile(src).containsKey("demo.Lead"));
    }
}
