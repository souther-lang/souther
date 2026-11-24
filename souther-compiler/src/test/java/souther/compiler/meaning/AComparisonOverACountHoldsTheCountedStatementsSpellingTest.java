package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison over counts of statements is spelled as the text its relation writes, and holds the
 * counted statements' spellings themselves: a count of a statement, a count of which statements
 * hold, and a sum over the elements of a count each hold what they count as its spelling. Written
 * out, the counted statement's text would be held again by every comparison over the count, and by
 * every count of a statement such a comparison is part of.
 */
class AComparisonOverACountHoldsTheCountedStatementsSpellingTest {

    private static final TermPath XS = TermPath.of("xs");
    private static final TermPath YS = TermPath.of("ys");

    private static Proposition truth(TermPath at) {
        return new Proposition.Truth(new DecisionSubject.AnInput(at), true);
    }

    /** A statement of more than one part about the element, which a count spells inside its own. */
    private static final Proposition STATED = new Proposition.Any(List.of(
            truth(XS.element().then("open")), truth(XS.element().then("late"))));

    private static final Quantity.HowManyMeet COUNTED =
            new Quantity.HowManyMeet(new DecisionSubject.AnInput(XS), STATED);

    private static final Quantity.HowManyHold WHICH_HOLD = new Quantity.HowManyHold(List.of(
            truth(TermPath.of("a")), new Proposition.All(List.of(truth(TermPath.of("b")),
                    truth(TermPath.of("c"))))));

    private static final Quantity.SumOver SUMMED =
            new Quantity.SumOver(new DecisionSubject.AnInput(YS), COUNTED);

    private static Proposition.Compared comparison(boolean holds) {
        Map<Quantity, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(COUNTED, ExactRatio.of(2));
        coefs.put(WHICH_HOLD, ExactRatio.of(-1));
        coefs.put(SUMMED, ExactRatio.of(3));
        Relation.OneWay<Quantity> one =
                Relation.OneWay.of(new LinearForm<>(ExactRatio.of(-5), coefs), Rel.GE);
        return new Proposition.Compared(new Relation.Affine(one.form(), one.proposition()), holds);
    }

    @Test
    void aComparisonIsSpelledAsItsRelationWrites() {
        for (boolean holds : new boolean[] {true, false}) {
            Proposition.Compared compared = comparison(holds);
            assertEquals((holds ? "" : "!") + compared.relation(), compared.spelledOut());
            assertEquals(compared.relation().toString(), compared.heldSpelling().toString());
        }
        for (Quantity each : List.of(COUNTED, WHICH_HOLD, SUMMED)) {
            assertEquals(each.spelled(), each.spelling().toString());
        }
    }

    @Test
    void aComparisonHoldsTheCountedStatementsSpellingsThemselves() {
        Spelling spelled = comparison(true).spelling();
        assertTrue(spelled.holdsWithin(STATED.spelling()), "the counted statement");
        for (Proposition each : WHICH_HOLD.each()) {
            assertTrue(spelled.holdsWithin(each.spelling()), "a statement whose holding is counted");
        }
        assertTrue(SUMMED.spelling().holdsWithin(STATED.spelling()), "the count inside a sum");
    }
}
