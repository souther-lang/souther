package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.math.BigInteger;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * Where making a value of a newtype stops a run, as far as its ends say.
 *
 * <p>The ends of a type are an outer bound of what its rules leave, and a rule can hold a number
 * out of them or leave two and none between. A construction is told as stopping a run outside
 * its ends only where they are the whole of what the rules say, so a run that makes a value at a
 * number the ends admit and the rules do not is never shown to get past the construction.
 */
class AConstructionIsToldAsARunOnlyWhereTheRulesLeaveTheWholeRunTest {

    private static NumericDomain.Bounds runOf(String declaration) {
        Compilation compilation = Compilation.ofSource("""
                module w1
                %s
                """.formatted(declaration), "Main");
        compilation.answerEverything();
        RuleReadingSource rules = RuleReadings.of(compilation, compilation.modules().get(0));
        assertNotNull(rules, "the model did not compile");
        TypeView view = TypeView.asWritten(
                new Type.Ref(TypeSymbols.declared(new TypeKey("w1", "Amount"))),
                rules.symbols(), rules.kinds(), rules.sums());
        return DeclaredBounds.wholeRunOf(view,
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES, TestDay.TODAY));
    }

    private static List<BigInteger> endsOf(NumericDomain.Bounds run) {
        return List.of(
                run.min() == null ? BigInteger.valueOf(-1) : run.min().wholeAdmitted(true),
                run.max() == null ? BigInteger.valueOf(-1) : run.max().wholeAdmitted(false));
    }

    @Test
    void aRunTheRulesLeaveWholeIsTheOneTheEndsGive() {
        NumericDomain.Bounds floor = runOf("data Amount = Int invariant value >= 0");
        assertNotNull(floor);
        assertEquals(BigInteger.ZERO, floor.min().wholeAdmitted(true));
        assertNull(floor.max());

        NumericDomain.Bounds above = runOf("data Amount = Int invariant value > 0");
        assertNotNull(above);
        assertEquals(BigInteger.ONE, above.min().wholeAdmitted(true));

        NumericDomain.Bounds between =
                runOf("data Amount = Int invariant value >= 0 && value <= 100");
        assertNotNull(between);
        assertEquals(List.of(BigInteger.ZERO, BigInteger.valueOf(100)), endsOf(between));
    }

    @Test
    void aRunWithANumberHeldOutOfItOrWithGapsIsNotShownWhole() {
        assertNull(runOf("data Amount = Int invariant value >= 0 && value /= 50"));
        assertNull(runOf("data Amount = Int invariant value == 0 || value == 100"));
        assertNull(runOf("data Amount = Int invariant Int.floorMod(value, 2) == 0"));
    }
}
