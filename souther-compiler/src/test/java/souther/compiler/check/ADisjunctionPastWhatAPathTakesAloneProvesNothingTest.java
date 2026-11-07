package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.observe.WorkFigure;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.query.ReadAs;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * One of several things is taken by taking each part alone, and the parts one reading of a
 * condition takes alone are held to a figure counted across every disjunction inside another.
 *
 * <p>Held on both sides of the figure. Every part taken and none leaving anything is nothing
 * reached, which is a proof; one part more than the figure lets is a part not taken, which may be
 * the one that leaves something, so the same disjunction proves nothing and says which figure
 * stopped it. Held over statements a path needs no tree, binding or position for: a part that
 * never holds leaves nothing, and one that always does leaves everything.
 */
class ADisjunctionPastWhatAPathTakesAloneProvesNothingTest {

    private static final int MOST = CompositionBudget.ALTERNATIVES_A_PATH_TRIES.maximum();

    private static final WhyNotTaken PAST_THE_FIGURE =
            new WhyNotTaken.MoreAlternativesThanAreTried(
                    CompositionBudget.ALTERNATIVES_A_PATH_TRIES.reached());

    /** A reading of terms that states no rules, which is all a proposition written out here asks. */
    private static final Terms TERMS = RuleReadings.termsOfNoClauseFiled(
            Symbols.none(DefaultStdlib.get()), ReadAs.THE_COMPILATION_DOES);

    private static Predicates.Assumed assumed(Proposition stated) {
        return MeaningAssumptions.assumed(stated, true, Known.top(), TERMS,
                MeaningAssumptions.InputPlaces.NONE, null);
    }

    /** One of {@code parts} things, none of which ever holds. */
    private static Proposition.Any noneHolding(int parts) {
        return new Proposition.Any(Collections.nCopies(parts, new Proposition.Always(false)));
    }

    @Test
    void asManyPartsAsAreTakenAloneLeavingNothingIsNothingReached() {
        Predicates.Assumed within = assumed(noneHolding(MOST));

        assertTrue(within.known().reachesNothing(), "every part was taken, and none leaves anything");
        assertEquals(List.of(), within.notTaken());
    }

    @Test
    void onePartMoreIsDeclinedAtTheFigureAndReachesSomething() {
        Predicates.Assumed past = assumed(noneHolding(MOST + 1));

        assertFalse(past.known().reachesNothing(),
                "a part not taken may be the one that leaves something");
        assertEquals(List.of(PAST_THE_FIGURE), past.notTaken());
    }

    /** Each disjunction inside stays under the figure alone, and the two of them and the parts
     *  holding them come to it — or to one past it. */
    @Test
    void thePartsInsideOneAnotherAreCountedTogether() {
        int inside = (MOST - 2) / 2;
        Proposition within = new Proposition.Any(List.of(noneHolding(inside),
                noneHolding(MOST - 2 - inside)));
        Proposition past = new Proposition.Any(List.of(noneHolding(inside),
                noneHolding(MOST - 1 - inside)));

        assertTrue(inside < MOST && MOST - 1 - inside < MOST, "each alone is within the figure");
        assertTrue(assumed(within).known().reachesNothing());
        assertEquals(List.of(), assumed(within).notTaken());
        assertFalse(assumed(past).known().reachesNothing());
        assertTrue(assumed(past).notTaken().contains(PAST_THE_FIGURE),
                () -> "together they are past it: " + assumed(past).notTaken());
    }

    /**
     * Two parts left, one of them only because a disjunction inside it was cut short, is no choice
     * a path's domain could not say: the part cut short may leave nothing. So the figure is named,
     * and the domain is not.
     */
    @Test
    void twoLeftWhereOneWasCutShortNameTheFigure() {
        List<Proposition> parts = new ArrayList<>();
        parts.add(new Proposition.Always(true));
        parts.add(noneHolding(MOST));
        Predicates.Assumed asked = assumed(new Proposition.Any(parts));

        assertFalse(asked.known().reachesNothing());
        assertEquals(List.of(PAST_THE_FIGURE), asked.notTaken());
    }

    /** A choice left between its parts is kept on the path, to be taken apart by what comes after. */
    @Test
    void twoLeftAreKeptUndecidedOnThePath() {
        Predicates.Assumed asked = assumed(new Proposition.Any(List.of(
                new Proposition.Always(true), new Proposition.Always(true))));

        assertEquals(1, asked.known().declinedChoices().size());
    }

    /**
     * What is said of a choice left undecided is said only of one the path still leaves: where the
     * rest of the condition reaches nothing, no part of the choice is left unread.
     */
    @Test
    void aChoiceUndecidedOnAPathThatReachesNothingSaysNothingWasLeftUnread() {
        Predicates.Assumed asked = assumed(new Proposition.All(List.of(
                new Proposition.Any(List.of(
                        new Proposition.Always(true), new Proposition.Always(true))),
                new Proposition.Always(false))));

        assertTrue(asked.known().reachesNothing());
        assertEquals(List.of(), asked.notTaken());
    }

    /** And two left where neither was cut short is the path's own limit, as it always was. */
    @Test
    void twoLeftThatWereBothTakenWholeNameThePathsLimit() {
        Predicates.Assumed asked = assumed(new Proposition.Any(List.of(
                new Proposition.Always(true), new Proposition.Always(true))));

        assertEquals(List.of(new WhyNotTaken.OutsideDomain(
                WhyNotTaken.DomainLimit.A_PATH_KNOWS_NO_ALTERNATIVES)), asked.notTaken());
    }

    /** Three whole numbers a behavior is handed, named as the parameters they are. */
    private static final MeaningAssumptions.InputPlaces NUMBERS = new MeaningAssumptions.InputPlaces(
            Map.of("n", parameter(0), "m", parameter(1), "k", parameter(2)), path -> Type.INT,
            Map.of(), Map.of());

    private static BindingId parameter(int at) {
        return new BindingId(new BindingOwner.OfValue("p", "f"), at);
    }

    /** That the number {@code input} is above nought. */
    private static Proposition aboveNought(String input) {
        return new Proposition.Compared(new Relation.Affine(LinearForm.<Quantity>atom(
                new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(TermPath.of(input)))),
                Rel.GT), true);
    }

    /**
     * A choice kept on the path is settled by a later condition against the parts the path
     * settles, which is another count than the one a reading takes alone. Where it runs out inside
     * the one part the choice comes to, the reading names the path's figure, at the figure and not
     * at what was left of it; with one part more left, the same choice comes to the choice its
     * second part is, which the path keeps and says it keeps.
     */
    @Test
    void aPartSettledPastWhatThePathSettlesNamesThePathsFigure() {
        Proposition first = aboveNought("n");
        Predicates.Assumed kept = MeaningAssumptions.assumed(new Proposition.Any(List.of(first,
                        new Proposition.Any(List.of(aboveNought("m"), aboveNought("k"))))),
                true, Known.top(), TERMS, NUMBERS, null);
        assertEquals(1, kept.known().declinedChoices().size(), "the choice is kept on the path");

        // The first part settling takes leaves nothing, and the second is a choice of its own, whose
        // two parts are taken alone after it: three parts left take the second in without its
        // last part, and four take it in whole.
        Predicates.Assumed past = MeaningAssumptions.assumed(first, false,
                kept.known().settledOverWhatIsKnown(3), TERMS, NUMBERS, null);
        Predicates.Assumed within = MeaningAssumptions.assumed(first, false,
                kept.known().settledOverWhatIsKnown(4), TERMS, NUMBERS, null);

        assertFalse(past.known().reachesNothing());
        assertFalse(past.shapeRead(), "a part was taken in without all of it");
        assertEquals(List.of(new WhyNotTaken.MoreAlternativesThanAreTried(
                        WorkFigure.PARTS_A_PATH_SETTLES.at(Known.Choices.PARTS_A_PATH_SETTLES))),
                past.notTaken());
        assertEquals(List.of(new WhyNotTaken.OutsideDomain(
                WhyNotTaken.DomainLimit.A_PATH_KNOWS_NO_ALTERNATIVES)), within.notTaken(),
                "taken in whole, the second part is the choice of its own the path keeps");
    }
}
