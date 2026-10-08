package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.meta.ModulePath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;

import java.math.BigDecimal;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the numbers of an input's readings leave is worked out once per question, across every
 * reading of that input.
 *
 * <p>A reading puts its numbers a question each time it is asked where a term runs, and the
 * readings a search makes from one another by fixing a position put the same question again
 * wherever they fixed the same thing. Counted rather than timed: what is held is that asking again
 * works nothing out, which is a shape and not a speed.
 */
class ReadingsOfOneInputWorkOutOneQuestionOnceTest {

    private static final String SOURCE = """
            module g

            data P = { lo: Int, hi: Int }
                invariant ordered = lo <= hi

            data Ok

            behavior read : (p: P) -> Ok
            """;

    private static final NumericTerm LO = new NumericTerm.ValueOf(TermPath.of("p").then("lo"));
    private static final NumericTerm HI = new NumericTerm.ValueOf(TermPath.of("p").then("hi"));

    /**
     * A fixed term asked about twice by one reading.
     *
     * <p>Fixed, because what one term is on its own is put onto the rules each time it is asked
     * about, and a fixing is something to put on — so each asking holds its own copy of the same
     * rules, and only the question they put is shared.
     */
    @Test
    void aTermAskedAboutAgainWorksNothingOutAgain() {
        ReadQuantities asked = quantities();
        Quantities fixed = asked.given(LO, count(3));
        long before = asked.closuresWorkedOut();
        fixed.runsBetween(LO);
        long once = asked.closuresWorkedOut();
        // Kept where the work is done, so asking again working nothing out is a count that stood
        // still and not a count nobody kept.
        assertTrue(once > before, "asking where a term runs worked nothing out");

        fixed.runsBetween(LO);

        assertEquals(once, asked.closuresWorkedOut());
    }

    @Test
    void twoReadingsFixingOnePositionAlikeShareWhatTheirRulesLeave() {
        ReadQuantities asked = quantities();
        Quantities first = asked.given(LO, count(3));
        assertEquals(Endpoint.inclusive(count(3)), first.runsBetween(HI).min(),
                "the rule holds hi at or above where lo is");
        first.emptiness();
        long once = asked.closuresWorkedOut();
        assertTrue(once > 0, "the first reading worked nothing out");

        Quantities second = asked.given(LO, count(3));
        second.runsBetween(HI);
        second.emptiness();

        assertEquals(once, asked.closuresWorkedOut(),
                "a second reading fixing lo where the first did closed its rules again");
    }

    private static ReadQuantities quantities() {
        Compilation compilation = Compilation.ofSources(List.of(SOURCE), ModulePath.EMPTY);
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        InputDomain read = InputDomain.of(sigs.get("read"),
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES),
                souther.compiler.carrier.Membership.none());
        return (ReadQuantities) read.quantities(rules);
    }

    private static Count count(int at) {
        return new Count(BigDecimal.valueOf(at));
    }
}
