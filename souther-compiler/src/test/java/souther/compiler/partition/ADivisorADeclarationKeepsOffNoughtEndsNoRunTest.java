package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A remainder ends a run only on a divisor of nought. Where the declarations hold
 * the divisor to numbers that leave nought out, whether the range is above it or below it, the
 * operation ends none and nothing is said unread; where they leave nought in, it may, and says so.
 */
class ADivisorADeclarationKeepsOffNoughtEndsNoRunTest {

    private static final String SOURCE = """
            module m1

            data Eaches = Int
                invariant value >= 0
            data PackSize = Int
                %s
            data Whole = { n: Int }
            data Part = { left: Int }

            behavior split : (eaches: Eaches, pack: PackSize) -> Whole | Part

            let split (eaches, pack) = {
                let leftover = %s
                guard leftover == 0 else Part { left = leftover }
                Whole { n = %s }
            }

            example split
            %s
            """;

    private static final String FLOOR_MOD = "Int.floorMod(eaches.value, pack.value)";

    private static final String ROWS_BY_TWELVE = """
                | "exact" : (Eaches(24), PackSize(12)) -> Whole { n = 1 }
                | "short" : (Eaches(25), PackSize(12)) -> Part { left = 1 }""";

    /** The comparisons the report says nothing is read of, or none. */
    private static List<String> notRead(String invariant, String leftover, String rows) {
        return notRead(invariant, leftover, "1", rows);
    }

    private static List<String> notRead(String invariant, String leftover, String whole,
                                        String rows) {
        Compilation compilation = Compilation.ofSource(
                SOURCE.formatted(invariant, leftover, whole, rows), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .filter(line -> line.contains("not read:"))
                .toList();
    }

    @Test
    void aRemainderByASizeOfAtLeastOneIsRead() {
        assertEquals(List.of(), notRead("invariant value >= 1", FLOOR_MOD, ROWS_BY_TWELVE));
    }

    @Test
    void aRemainderByASizeBelowNoughtIsRead() {
        String rows = """
                | "exact" : (Eaches(24), PackSize(-12)) -> Whole { n = 1 }
                | "short" : (Eaches(25), PackSize(-12)) -> Part { left = -11 }""";
        assertEquals(List.of(), notRead("invariant value <= -1", FLOOR_MOD, rows));
    }

    /** The quotient is worked out after the comparison, so it is no stop of the rows the guard
     *  lets through; the remainder before it is what the divisor's declaration decides. */
    @Test
    void aRoundedQuotientAfterTheGuardLeavesARemainderByASizeRead() {
        String quotient = "Rational.toInt(DOWN, eaches.value / pack.value)";
        String rows = """
                | "exact" : (Eaches(24), PackSize(12)) -> Whole { n = 2 }""";
        assertEquals(List.of(), notRead("invariant value >= 1", FLOOR_MOD, quotient, rows));
        assertFalse(notRead("", FLOOR_MOD, quotient, rows).isEmpty());
    }

    @Test
    void aRemainderByAnIntThatMayBeNoughtIsNotRead() {
        assertFalse(notRead("", FLOOR_MOD, ROWS_BY_TWELVE).isEmpty());
    }

    @Test
    void aRemainderByASizeThatReachesNoughtIsNotRead() {
        String rows = """
                | "exact" : (Eaches(24), PackSize(1)) -> Whole { n = 1 }""";
        assertFalse(notRead("invariant value >= -1 && value <= 1", FLOOR_MOD, rows).isEmpty());
    }
}
