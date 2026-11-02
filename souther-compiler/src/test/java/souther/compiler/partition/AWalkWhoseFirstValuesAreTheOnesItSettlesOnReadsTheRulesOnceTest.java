package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.partition.ScriptedRegion.Script;

import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * A search whose first value at every position is the one it settles on reads the rules once for
 * the whole assignment, and not once for each position fixed — and finds what the walk finds.
 *
 * <p>Counted where the answer is the same either way, because what is held is the work: the first
 * value of each position in the order the search tries them, the last position solved. Each reading
 * of the rules with a position fixed is a closure of every rule reaching the form's positions, and a
 * search of six positions that read them for each was most of what a witness cost.
 *
 * <p>And compared with the walk where the readings on the way to an assignment say more than the
 * reading of the assignment does. The descent skips those readings, so it is only as good as the
 * region's word that the reading of a whole assignment is settled
 * ({@link SearchRegion#emptinessIsSettled}): a region shown empty is then shown empty with more
 * fixed. Each region here answers as a script says, one answer for the regions on the way and
 * another for the whole assignment, which is what a reading that stopped short of the end does.
 */
class AWalkWhoseFirstValuesAreTheOnesItSettlesOnReadsTheRulesOnceTest {

    private static final NumericTerm.FromOnePosition X = position("p.x");
    private static final NumericTerm.FromOnePosition Y = position("p.y");
    private static final NumericTerm.FromOnePosition Z = position("p.z");

    private static NumericTerm.FromOnePosition position(String path) {
        return new NumericTerm.ValueOf(TermPath.of(path));
    }

    private static Count at(long value) {
        return new Count(BigDecimal.valueOf(value));
    }

    private static boolean fixedAtNought(Map<NumericTerm, Place> standing, NumericTerm term) {
        return at(0).equals(standing.get(term));
    }

    /** Every position of the form, read and written on the whole numbers. */
    private static Map<NumericTerm, TermOrders> wholeNumbers() {
        Map<NumericTerm, TermOrders> on = new LinkedHashMap<>();
        for (NumericTerm.FromOnePosition each : List.of(X, Y, Z)) {
            on.put(each, TermOrdersFixtures.itself(each, new Carrier.Whole()));
        }
        return on;
    }

    private static Realization realizedAt(LevelRealizer realizer, int level,
                                          Map<NumericTerm, ExactRatio> weights,
                                          SearchRegion within) {
        Standing standing = new BorderQuantity.OverAForm("decide",
                new LinearForm<NumericTerm>(ExactRatio.ZERO, weights), wholeNumbers())
                .standingAt(new Criterion.AtTheLevel(Level.OfTheQuantity.of(level)));
        return realizer.realize(standing, within,
                NothingTheDeclarationsRefuse.at(TermPath.of("p.x"), TermPath.of("p.y"),
                        TermPath.of("p.z")));
    }

    private static Realization realizedAt(LevelRealizer realizer, int level, SearchRegion within) {
        return realizedAt(realizer, level,
                Map.of(X, ExactRatio.ONE, Y, ExactRatio.ONE, Z, ExactRatio.ONE), within);
    }

    private static Map<RealizationTarget, Place> found(Realization realization) {
        return assertInstanceOf(Realization.Found.class, realization).fixing();
    }

    private static Map<RealizationTarget, Place> assignment(long x, long y, long z) {
        return Map.of(RealizationTarget.of(X), at(x), RealizationTarget.of(Y), at(y),
                RealizationTarget.of(Z), at(z));
    }

    /**
     * {@code x + y + z = 6}, each from nought to ten: the first value of {@code x} is nought, of
     * {@code y} nought, and {@code z} is six. The rules are read for the assignment and for none of
     * the positions fixed on the way.
     */
    @Test
    void theRulesAreReadOnceForTheAssignmentAndNotForEachPositionFixed() {
        ScriptedRegion region = ScriptedRegion.of(Script.refusingNothing());

        Realization found = realizedAt(new LevelRealizer(), 6, region);

        assertEquals(assignment(0, 0, 6), found(found),
                "the first value of each position, and the last solved");
        assertEquals("emptiness=5 fixed=2",
                "emptiness=" + region.counts().emptiness.get() + " fixed="
                        + region.counts().fixed.get(),
                "the item's own readings around the search and the one of the assignment; the"
                        + " walk adds one of each for every position it fixes before the last,"
                        + " which is two here");
    }

    /**
     * And where the rules refuse the first assignment, the walk finds the next one: {@code x} at
     * nought is refused, so the walk fixes {@code x} at one, {@code y} at nought and solves
     * {@code z} at five.
     */
    @Test
    void anAssignmentTheRulesRefuseLeavesTheWalkToFindTheNext() {
        Script script = Script.refusing(standing -> fixedAtNought(standing, X));

        assertEquals(assignment(1, 0, 5),
                found(realizedAt(new LevelRealizer(), 6, ScriptedRegion.of(script))));
        assertEquals(assignment(1, 0, 5),
                found(realizedAt(new LevelRealizer().walkingOnly(), 6, ScriptedRegion.of(script))));
    }

    /**
     * A region that shows {@code x} at nought empty and then does not show the assignment that
     * holds it empty is one the descent has no business trusting.
     *
     * <p>Allowed by the contract of {@link SearchRegion#emptiness}, which is a proof where it
     * answers and nothing where it does not. What the descent leans on is the region saying the
     * reading of the whole assignment is settled, and this one does not.
     */
    @Test
    void aReadingThatStoppedShortOfTheEndLeavesTheWalkToSkipWhatItProved() {
        Script script = Script.refusing(standing -> standing.size() == 1
                && fixedAtNought(standing, X)).unsettled();

        assertEquals(assignment(1, 0, 5),
                found(realizedAt(new LevelRealizer(), 6, ScriptedRegion.of(script))),
                "what the walk finds, which skips x at nought on the way");
        assertEquals(assignment(1, 0, 5),
                found(realizedAt(new LevelRealizer().walkingOnly(), 6, ScriptedRegion.of(script))));
    }

    /**
     * And the same region saying its reading is settled is the descent's to trust, so what it
     * hands back is an assignment the walk skipped.
     *
     * <p>Held to show where the protection is: the word of the region, not a coincidence of the
     * models searched.
     */
    @Test
    void aRegionSayingItIsSettledWhereItIsNotIsTakenAtItsWord() {
        Script script = Script.refusing(standing -> standing.size() == 1
                && fixedAtNought(standing, X));

        assertNotEquals(
                found(realizedAt(new LevelRealizer().walkingOnly(), 6, ScriptedRegion.of(script))),
                found(realizedAt(new LevelRealizer(), 6, ScriptedRegion.of(script))),
                "the descent took the assignment the region did not show empty");
    }

    /**
     * Where fixing {@code x} at nought leaves {@code y} a run that starts at one, the walk's first
     * value of {@code y} is one, not the nought the run before anything was fixed starts at.
     */
    @Test
    void aRunTheFixedPositionsNarrowIsWalkedFromWhereItStarts() {
        Script script = Script.refusing(standing -> fixedAtNought(standing, X)
                        && fixedAtNought(standing, Y))
                .runningFrom((standing, term) -> term == Y && fixedAtNought(standing, X)
                        ? new NumericDomain.Bounds(Endpoint.inclusive(at(1)),
                                Endpoint.inclusive(at(10)))
                        : ScriptedRegion.ZERO_TO_TEN);

        Map<RealizationTarget, Place> byTheWalk =
                found(realizedAt(new LevelRealizer().walkingOnly(), 6, ScriptedRegion.of(script)));

        assertEquals(assignment(0, 1, 5), byTheWalk);
        assertEquals(byTheWalk,
                found(realizedAt(new LevelRealizer(), 6, ScriptedRegion.of(script))));
    }

    /**
     * A region may read a run more coarsely once a position is fixed: here {@code y} runs from one
     * before anything is fixed and from nought once {@code x} is, and nothing is shown empty. The
     * walk takes the first value of {@code y} from the second, so the descent, which takes it from
     * the first, would not find what the walk finds. A region that does not say its runs only
     * narrow when a position is fixed is not one the descent is taken over.
     */
    @Test
    void aRunThatWidensOnceAPositionIsFixedLeavesTheFirstValueToTheWalk() {
        Script widening = widening();

        assertEquals(assignment(0, 0, 6),
                found(realizedAt(new LevelRealizer().walkingOnly(), 6, ScriptedRegion.of(widening))));
        assertEquals(assignment(0, 0, 6),
                found(realizedAt(new LevelRealizer(), 6, ScriptedRegion.of(widening))),
                "the walk's, since the region does not say its runs only narrow");
    }

    /**
     * And the same runs said to only narrow are taken at that word, so what comes back is not the
     * walk's.
     *
     * <p>Held to show where the protection is, as with the word about the reading: the region's.
     */
    @Test
    void aRegionSayingItsRunsOnlyNarrowWhereTheyWidenIsTakenAtItsWord() {
        Script lying = widening().sayingTheyNarrow();

        assertNotEquals(
                found(realizedAt(new LevelRealizer().walkingOnly(), 6, ScriptedRegion.of(lying))),
                found(realizedAt(new LevelRealizer(), 6, ScriptedRegion.of(lying))));
    }

    /**
     * A region that says its runs only narrow, but not for a number the search holds, is one the
     * descent is not taken over: the word is asked of the numbers the search fixes.
     */
    @Test
    void aNumberTheRegionHasNotBeenHeldForLeavesTheSearchToTheWalk() {
        Script script = widening().sayingTheyNarrow().notVouchingFor(term -> term.equals(Z));

        assertEquals(assignment(0, 0, 6),
                found(realizedAt(new LevelRealizer(), 6, ScriptedRegion.of(script))),
                "the walk's, since the region does not vouch for z");
    }

    private static Script widening() {
        return Script.refusingNothing().runningFromWithoutSayingTheyNarrow(
                (standing, term) -> term == Y && standing.isEmpty()
                        ? new NumericDomain.Bounds(Endpoint.inclusive(at(1)),
                                Endpoint.inclusive(at(10)))
                        : ScriptedRegion.ZERO_TO_TEN);
    }

    /**
     * Where the arithmetic cannot hold what is owed the walk comes back short, and the descent
     * leaves it to say so rather than answering over it.
     *
     * <p>{@code x} weighs a number too large for what is owed after it to be written beside, and
     * runs from one, so its first value leaves an amount no ratio holds.
     */
    @Test
    void anAmountTheArithmeticCannotHoldIsLeftToTheWalk() {
        ExactRatio huge = ExactRatio.of(new BigDecimal("1e1500000000"));
        Map<NumericTerm, ExactRatio> weights =
                Map.of(X, huge, Y, ExactRatio.ONE, Z, ExactRatio.ONE);
        Script script = Script.refusingNothing().runningFrom((standing, term) -> term == X
                ? new NumericDomain.Bounds(Endpoint.inclusive(at(1)), Endpoint.inclusive(at(10)))
                : ScriptedRegion.ZERO_TO_TEN);

        Realization byTheWalk = realizedAt(new LevelRealizer().walkingOnly(), 6, weights,
                ScriptedRegion.of(script));

        assertNotEquals(Realization.Found.class, byTheWalk.getClass(),
                "nothing was composed over an amount the arithmetic cannot hold");
        assertEquals(byTheWalk,
                realizedAt(new LevelRealizer(), 6, weights, ScriptedRegion.of(script)));
    }
}
