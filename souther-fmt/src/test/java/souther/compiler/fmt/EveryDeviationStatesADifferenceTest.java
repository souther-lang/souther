package souther.compiler.fmt;

import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import souther.compiler.cst.CstParser;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A line of the report says what differs.
 *
 * <p>A different property from the one its sibling holds. That a departure is named by some rule is
 * about the report having a line; this is about the line saying something. A report can name every
 * departure a source has and still print, against one of them, the same words on both sides — which
 * is a line that refutes itself, and no count of what is covered would show it.
 *
 * <p>The two answers are what a reader acts on. A rule whose verdict is a choice between two forms
 * has to quote the choice at the place the source made the other one, and a construct can differ
 * from the canonical form in a way that is not the choice the rule as a whole made: it broke down
 * the page as it should have, and one of the places it settles was run together.
 */
@Tag("population")
class EveryDeviationStatesADifferenceTest {

    /**
     * A module header long enough that the width decides it, so the group under test is the width
     * rule's own rather than one broken by something inside it.
     */
    private static final String EXPOSING =
            "module example.pipeline exposing (Alpha, Beta, Gamma, Delta, Epsilon, Zeta, Eta, "
                    + "Theta, Iota, Kappa)\n";

    private static String canonical(String source) {
        return Formatter.format(CstParser.parse(source).root());
    }

    /** {@code line} of {@code text}, one-based, run onto the line before it. */
    private static String join(String text, int line) {
        List<String> lines = new ArrayList<>(List.of(text.split("\n", -1)));
        String moved = lines.remove(line - 1).stripLeading();
        lines.set(line - 2, lines.get(line - 2) + " " + moved);
        return String.join("\n", lines);
    }

    private static Deviations.Deviation only(Deviations.Report report, String rule) {
        List<Deviations.Deviation> found = new ArrayList<>();
        for (Deviations.Deviation d : report.deviations()) {
            if (d.rule().contains(rule)) {
                found.add(d);
            }
        }
        assertEquals(1, found.size(),
                "this rule answers once: " + rule + " in " + report.deviations());
        return found.get(0);
    }

    /** Every line of every report over the sweep quotes two different answers. */
    @ParameterizedTest(name = "{0}")
    @MethodSource("souther.compiler.fmt."
            + "EveryDepartureFromTheCanonicalFormIsSomeRulesTest#departures")
    void aDeviationQuotesTwoDifferentAnswers(
            EveryDepartureFromTheCanonicalFormIsSomeRulesTest.Departure departure) {
        Deviations.Report report = departure.report();

        for (Deviations.Deviation d : report.deviations()) {
            assertNotEquals(d.canonical(), d.source(),
                    "this line reports a difference and quotes the same words on both sides: "
                            + d.rule() + "\n" + departure.text());
        }
    }

    /**
     * And the sweep asks it of the rules the property was written for. Held over candidates it
     * never reaches, the check above is a check of nothing.
     */
    @Test
    void andTheSweepReachesBothOfTheGroupRules() {
        int width = 0;
        int places = 0;
        for (EveryDepartureFromTheCanonicalFormIsSomeRulesTest.Departure departure
                : EveryDepartureFromTheCanonicalFormIsSomeRulesTest.departures().toList()) {
            for (Deviations.Deviation d : departure.report().deviations()) {
                if (d.rule().contains("exceed the width")) {
                    width++;
                } else if (d.rule().contains("breaks at every place it settles")) {
                    places++;
                }
            }
        }

        assertTrue(width > 0, "no candidate in the sweep is answered by the width rule");
        assertTrue(places > 0, "no candidate in the sweep ran a place of a construct together");
    }

    /**
     * A construct the canonical form writes down the page for a reason of its own is answered by
     * that reason, and not by the width.
     *
     * <p>The rule names a cause: a line that would exceed the width breaks. A construct written
     * down the page because it holds something that cannot share a line was never measured against
     * the width, and a source told this would be looking for a line that is not too long.
     */
    @Test
    void aConstructPutDownThePageByWhatItHoldsIsNotAnsweredByTheWidth() {
        String source = "module fmtprobe exposing ( f )\n\n"
                + "let f (opt: Option<Int>): Int = match opt with | Some v -> v | None -> 0\n";

        Deviations.Report report = Deviations.of(source);

        boolean said = false;
        for (Deviations.Deviation d : report.deviations()) {
            assertTrue(!d.rule().contains("exceed the width"),
                    "the width decided nothing about this construct: " + d);
            if (d.rule().contains("writes its members one to a line")
                    && "down the page".equals(d.canonical()) && "on one line".equals(d.source())) {
                said = true;
            }
        }
        assertTrue(said, "the obligation that put it down the page says so: "
                + report.deviations());
    }

    /**
     * A group written down the page whose source ran one of its places together differs there, and
     * the line says so.
     *
     * <p>Not the width rule. Both texts write this construct down the page, so the width decided
     * nothing the two disagree about; what differs is the place, and the rule a reader is held to
     * is the one about the places a construct written down the page breaks at.
     *
     * <p>And the place is not the group's first. A report that answered every one of these at the
     * head of the construct would be right about the construct and useless about the source: what
     * the author has to look at is the line they ran together.
     */
    @Test
    void aPlaceRunTogetherIsAnsweredWhereItWasRunTogether() {
        String canonical = canonical(EXPOSING);
        String source = join(canonical, 6);   // Epsilon onto the line Delta is on

        Deviations.Deviation d = only(Deviations.of(source), "breaks at every place it settles");

        assertEquals(5, d.line(), "answered at the place that was run together: " + d);
        assertNotEquals(d.canonical(), d.source(), "and it says what differs there: " + d);
    }

    /** Wherever it was run together. The last of a construct's places is one of them. */
    @Test
    void andAtTheLastOfThemToo() {
        String canonical = canonical(EXPOSING);
        String source = join(canonical, 12);   // the closing bracket onto the last member

        Deviations.Deviation d = only(Deviations.of(source), "breaks at every place it settles");

        assertEquals(11, d.line(), "answered at the place that was run together: " + d);
        assertNotEquals(d.canonical(), d.source(), "and it says what differs there: " + d);
    }

    /**
     * A source that ran the whole construct together is answered about the construct, by the rule
     * that decided its form.
     *
     * <p>This is what the width rule is for: the two texts disagree about whether the construct is
     * written down the page at all, and the width is why the canonical form's answer is what it is.
     */
    @Test
    void aConstructRunTogetherAltogetherIsAnsweredByTheRuleThatDecidedItsForm() {
        Deviations.Deviation d = only(Deviations.of(EXPOSING), "exceed the width");

        assertEquals(1, d.line(), "answered at the first place it should have broken: " + d);
        assertEquals("down the page", d.canonical(), "the canonical form writes it down: " + d);
        assertEquals("on one line", d.source(), "and the source wrote it whole: " + d);
    }
}
