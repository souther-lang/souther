package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * What several ways of holding a row come to together, and what is left of them once some are
 * set aside, said by the answer and never read off a list being empty
 * ({@link HeldOutcome.Bringing#oneOf}, {@link HeldOutcome.Bringing.Found#keeping}).
 *
 * <p>Three ways of nothing — no row takes it, nothing here worked it out, a figure stopped the
 * looking — and a list that came to none is any of them. Read as no row taking it where a figure
 * left ways unlooked at, a way past a guard down which a row goes is said to be one no row goes,
 * or one that would write a stated value afresh where only the ways looked at would.
 */
class WaysOfHoldingARowAreAnsweredTogetherByOneLawTest {

    private static final HeldOutcome.Bringing NO_ROW = new HeldOutcome.Bringing.NoValueCanStandThere();

    private static final HeldOutcome.Bringing SHORT = new HeldOutcome.Bringing.NothingFound();

    private static final HeldOutcome.Bringing STOPPED = new HeldOutcome.Bringing.LeftUnlooked(
            Set.of(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT));

    @Test
    void noRowTakesItOnlyWhereNoRowTakesAnyOfThem() {
        assertInstanceOf(HeldOutcome.Bringing.NoValueCanStandThere.class,
                HeldOutcome.Bringing.oneOf(List.of(NO_ROW, NO_ROW)));
        assertInstanceOf(HeldOutcome.Bringing.NothingFound.class,
                HeldOutcome.Bringing.oneOf(List.of(NO_ROW, SHORT)));
        assertInstanceOf(HeldOutcome.Bringing.NothingFound.class,
                HeldOutcome.Bringing.oneOf(List.of()));
    }

    @Test
    void aFigureThatStoppedSomeLookingIsSaidOverWhatTheRestCameTo() {
        assertEquals(STOPPED, HeldOutcome.Bringing.oneOf(List.of(NO_ROW, STOPPED, SHORT)));
    }

    /** Two figures that stopped two lookings are both said: each is a number to raise. */
    @Test
    void theFiguresThatStoppedSeveralLookingsAddUp() {
        assertEquals(new HeldOutcome.Bringing.LeftUnlooked(Set.of(
                        CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT,
                        CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG)),
                HeldOutcome.Bringing.oneOf(List.of(STOPPED, new HeldOutcome.Bringing.LeftUnlooked(
                        Set.of(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG)))));
    }

    @Test
    void aWayFoundIsTheAnswerWithTheFigureThatLeftOthersOut() {
        HeldOutcome way = aWay();
        assertEquals(new HeldOutcome.Bringing.Found(List.of(way),
                        Set.of(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT)),
                HeldOutcome.Bringing.oneOf(List.of(SHORT,
                        new HeldOutcome.Bringing.Found(List.of(way), Set.of()), STOPPED)));
    }

    @Test
    void noneKeptOfWaysAFigureLeftSomeOfIsNotNoneKept() {
        HeldOutcome way = aWay();
        assertEquals(new HeldOutcome.Bringing.Kept.NoneLookedAtWas(
                        Set.of(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG)),
                new HeldOutcome.Bringing.Found(List.of(way),
                        Set.of(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG))
                        .keeping(_ -> false));
        assertInstanceOf(HeldOutcome.Bringing.Kept.None.class,
                new HeldOutcome.Bringing.Found(List.of(way), Set.of())
                        .keeping(_ -> false));
    }

    /**
     * The parts of one way, which a row is held to all at once: every figure that left a part
     * unlooked at, and every reason a part cannot be held, are said together; a part no row goes
     * settles the way.
     */
    @Test
    void thePartsOfAWaySayEveryFigureAndEveryReasonTogether() {
        Generator.PartsHeld figures = Generator.partsHeld(List.of(STOPPED,
                new HeldOutcome.Bringing.LeftUnlooked(
                        Set.of(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG))), _ -> true);
        assertEquals(Set.of(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT,
                CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG), figures.unlooked());
        Generator.PartsHeld reasons = Generator.partsHeld(List.of(SHORT,
                new HeldOutcome.Bringing.Found(List.of(aWay()), Set.of())), _ -> false);
        assertEquals(Set.of(RepairShortfall.Barrier.NOTHING_HOLDS_A_ROW_TO_IT,
                RepairShortfall.Barrier.IT_WOULD_REWRITE_A_STATED_VALUE), reasons.why());
        assertEquals(true, Generator.partsHeld(List.of(SHORT, NO_ROW), _ -> true).noRowGoes());
    }

    /** One way of holding a row, to a truth of {@code open}, over nothing on the way. */
    private static HeldOutcome aWay() {
        return new HeldOutcome(List.of(new RowDemand.ATruth(TermPath.of("open"), true)),
                List.of(), WayToTheBorder.UNTOUCHED, Map.of(), Reachability.untouched(region()));
    }

    private static SearchRegion region() {
        Compilation compilation = Compilation.ofSource("""
                module m

                behavior f : (open: Bool) -> Int
                let f (open) = if open then 1 else 0
                """, "Main");
        String module = compilation.modules().get(0);
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        Map<String, InputDomain> inputs =
                compilation.db().ask(new Adequacy.Inputs(module)).value();
        return inputs.get("f").reading(rules).quantities().region();
    }
}
