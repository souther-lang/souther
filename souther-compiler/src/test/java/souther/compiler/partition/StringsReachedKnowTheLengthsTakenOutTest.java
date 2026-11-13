package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.TypeCardinality;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.PositionBounds;
import souther.compiler.inputs.RepresentationBounds;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the strings of a position reach is the lengths its rules leave it, and a length the rules
 * take out from between the ends they place is the length of none of its strings: no line drawn
 * there is at a length a row can be written at, and a length either side of it is one.
 */
class StringsReachedKnowTheLengthsTakenOutTest {

    private static final String MODEL = """
            module reach

            data Code = String invariant %s

            data Ok

            behavior read : (code: Code) -> Ok
            """;

    private static StringsReached reachedBy(String rule, NumericTerm[] length) {
        Compilation compilation = Compilation.ofSources(List.of(MODEL.formatted(rule)),
                souther.compiler.meta.ModulePath.EMPTY);
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext reading =
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        InputDomain input = InputDomain.of(sigs.get("read"), reading,
                TypeCardinality.Counts.workedOutIn(reading),
                souther.compiler.carrier.Membership.none());
        List<Position> positions = input.positions();
        for (Position each : positions) {
            for (PositionBounds bounds : each.bounds()) {
                if (bounds.term() instanceof NumericTerm.TakenOf taken
                        && RepresentationBounds.isALength(taken)) {
                    length[0] = bounds.term();
                }
            }
        }
        assertNotNull(length[0], "the code has a length");
        return StringsReached.of(positions);
    }

    @Test
    void aLineAtALengthTakenOutIsAtTheLengthOfNoString() {
        NumericTerm[] length = new NumericTerm[1];
        StringsReached reached = reachedBy(
                "String.length(value) <= 10 && String.length(value) /= 7", length);
        assertFalse(reached.allowsAnEdgeAt(length[0], ExactRatio.of(7)),
                "no string has seven code points");
        assertTrue(reached.allowsAnEdgeAt(length[0], ExactRatio.of(6)));
        assertTrue(reached.allowsAnEdgeAt(length[0], ExactRatio.of(8)));
        assertTrue(reached.allowsAnEdgeAt(length[0], ExactRatio.of(0)));
    }

    /**
     * A value is shown to exist where some string is in the set and has a length the rules leave.
     * The set admits the strings of the lengths taken out as well, so what it holds is not enough:
     * a set whose every string is of a length taken out holds no value of the position.
     */
    @Test
    void aSetWhoseEveryStringIsOfALengthTakenOutLeavesNoValue() {
        Map<String, Boolean> exists = new LinkedHashMap<>();
        exists.put("value == \"abc\" && String.length(value) /= 3", false);
        exists.put("value == \"abc\" && (String.length(value) < 3 || String.length(value) > 3)",
                false);
        exists.put("String.matches(\"aaa\", value) && String.length(value) /= 3", false);
        exists.put("(value == \"abc\" || value == \"abcd\") && String.length(value) /= 3", true);
        exists.put("String.matches(\"a+\", value) && String.length(value) /= 3", true);
        exists.put("String.length(value) <= 10 && String.length(value) /= 7", true);
        exists.forEach((rule, there) -> assertEquals(there,
                reachedBy(rule, new NumericTerm[1]).mandatoryPositionsHoldAValue(), rule));
    }

    @Test
    void theSameLineWhereNoLengthIsTakenOutIsAtAStringsLength() {
        NumericTerm[] length = new NumericTerm[1];
        StringsReached reached = reachedBy("String.length(value) <= 10", length);
        assertTrue(reached.allowsAnEdgeAt(length[0], ExactRatio.of(7)));
        assertTrue(reached.lengthsLeft().get(length[0]).isOneRun(),
                "the lengths left are the one run between the ends");
    }

    @Test
    void aChoiceBetweenRunsTakesTheLengthsBetweenThemOut() {
        NumericTerm[] length = new NumericTerm[1];
        StringsReached reached = reachedBy("String.length(value) <= 10"
                + " && (String.length(value) < 3 || String.length(value) > 5)", length);
        for (int taken : List.of(3, 4, 5)) {
            assertFalse(reached.allowsAnEdgeAt(length[0], ExactRatio.of(taken)),
                    "a line at " + taken);
        }
        for (int left : List.of(0, 2, 6, 10)) {
            assertTrue(reached.allowsAnEdgeAt(length[0], ExactRatio.of(left)), "a line at " + left);
        }
    }
}
