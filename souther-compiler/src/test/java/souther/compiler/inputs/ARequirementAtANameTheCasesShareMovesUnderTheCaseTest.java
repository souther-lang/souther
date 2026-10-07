package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A requirement stated at a name the cases of a sum share stays at the name until something says
 * which case the value is, and is then the requirement at the position under that case.
 *
 * <p>Built on crossings made here rather than on a model's reading, so that the order requirements
 * are put together in and the depth of the sums can be chosen. An optional's two carriers stand in
 * for a sum's cases, and for the values a fork leaves at the name: to the merge both are cases of a
 * position, and two of them at one position hold together where they share one.
 */
class ARequirementAtANameTheCasesShareMovesUnderTheCaseTest {

    private static final TermPath LEAD = TermPath.of("lead");
    private static final Refinement ONE = Refinement.of(new Case.Presence(true));
    private static final Refinement OTHER = Refinement.of(new Case.Presence(false));

    /** {@code lead.flag}, read on the value at {@code lead} and standing under each case. */
    private static final TermPath FLAG = LEAD.then("flag");
    private static final List<NameReach.Crossing> UNDER_BOTH = List.of(
            new NameReach.Crossing(LEAD, "flag", ONE, LEAD.refine(ONE).then("flag")),
            new NameReach.Crossing(LEAD, "flag", OTHER, LEAD.refine(OTHER).then("flag")));

    /** What a fork on the name requires on its arm leaving {@code left}. */
    private static Requirements atTheName(Refinement left) {
        return Requirements.of(FLAG.refine(left), UNDER_BOTH);
    }

    private static Requirements theCase(Refinement which) {
        return Requirements.NONE.and(LEAD, which);
    }

    private static Requirements merged(Requirements.Merge merge) {
        return assertInstanceOf(Requirements.Merge.Merged.class, merge).requirements();
    }

    @Test
    void untilACaseIsChosenItStaysAtTheName() {
        Requirements asked = atTheName(ONE);
        assertEquals(Map.of(FLAG, CasesLeft.of(ONE)), asked.refinements());
        assertEquals(List.of(FLAG), asked.atANameTheCasesShare());
        assertEquals(UNDER_BOTH, asked.crossings());
    }

    /** Whichever side chooses the case, and whether by merging or by adding it. */
    @Test
    void choosingTheCaseMovesItUnderThatCase() {
        Requirements expected = new Requirements(Map.of(LEAD, CasesLeft.of(OTHER),
                LEAD.refine(OTHER).then("flag"), CasesLeft.of(ONE)), List.of());
        assertEquals(expected, merged(atTheName(ONE).merge(theCase(OTHER))));
        assertEquals(expected, merged(theCase(OTHER).merge(atTheName(ONE))));
        assertEquals(expected, atTheName(ONE).and(LEAD, OTHER));
        assertEquals(List.of(), expected.atANameTheCasesShare());
    }

    @Test
    void movedItMeetsWhatIsAskedUnderTheCase() {
        Requirements underTheCase = LEAD.refine(ONE).then("flag").refine(OTHER).requirements();
        Requirements.Merge.Conflict against = assertInstanceOf(Requirements.Merge.Conflict.class,
                atTheName(ONE).merge(underTheCase));
        assertEquals(LEAD.refine(ONE).then("flag"), against.at());

        Requirements agreeing = LEAD.refine(OTHER).then("flag").refine(ONE).requirements();
        assertEquals(CasesLeft.of(ONE), merged(atTheName(ONE).merge(agreeing))
                .at(LEAD.refine(OTHER).then("flag")));
    }

    /** A name under two sums is moved by the outer one, and then by the inner one. */
    @Test
    void aNameTwoSumsDownMovesUnderBoth() {
        TermPath inner = LEAD.refine(ONE);
        List<NameReach.Crossing> twice = List.of(
                new NameReach.Crossing(LEAD, "flag", ONE, inner.then("flag")),
                new NameReach.Crossing(inner, "flag", OTHER, inner.refine(OTHER).then("flag")));
        Requirements asked = Requirements.of(FLAG.refine(ONE), twice);
        assertEquals(twice, asked.crossings(), "both are still to cross");

        Requirements outer = merged(asked.merge(theCase(ONE)));
        assertEquals(List.of(inner.then("flag")), outer.atANameTheCasesShare(),
                "under the outer case it is a name the inner one's cases share");
        Requirements both = merged(outer.merge(Requirements.NONE.and(inner, OTHER)));
        assertEquals(CasesLeft.of(ONE), both.at(inner.refine(OTHER).then("flag")));
        assertNull(both.at(inner.then("flag")));
        assertEquals(List.of(), both.crossings());
    }

    /** A requirement whose case is chosen is the one at the position, and never the name's. */
    @Test
    void aNameLeftAboveAChosenCaseIsRefused() {
        assertThrows(IllegalArgumentException.class, () -> new Requirements(
                Map.of(LEAD, CasesLeft.of(ONE), FLAG, CasesLeft.of(ONE)), UNDER_BOTH));
    }
}
