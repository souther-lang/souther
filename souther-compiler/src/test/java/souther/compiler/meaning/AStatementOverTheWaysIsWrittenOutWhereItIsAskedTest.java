package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A statement over the ways its elements are kept is held as what its cases are written out from.
 * Holding it, telling it from another and denying it write nothing out; asking for its cases
 * does, once. How many ways there are is the work of writing them out and not how many parts they
 * come to, so ways that all state alike are read however many they are, up to the work that is
 * done; and a number that no way can hold is found where the cases are written, whichever way
 * the statement is asked about.
 */
class AStatementOverTheWaysIsWrittenOutWhereItIsAskedTest {

    private static final Quantity.TheKeptTotal SUM = new Quantity.TheKeptTotal(1, false);

    private static Proposition truth(String at) {
        return new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of(at)), true);
    }

    /** {@code total >= 1}. */
    private static Proposition totalAtLeastOne() {
        LinearForm<Quantity> form = LinearForm.<Quantity>atom(SUM)
                .plus(LinearForm.<Quantity>constant(ExactRatio.of(-1))).orNull();
        Relation.OneWay<Quantity> oneWay = Relation.OneWay.of(form, Rel.GE);
        return Proposition.compared(
                new Relation.Affine(oneWay.form(), oneWay.proposition()), oneWay.holds());
    }

    /** Elements numbered from nought, each kept by a truth of its own. */
    private static KeptWays eachKeptByItsOwnTruth(int elements) {
        return new KeptWays(IntStream.range(0, elements)
                .mapToObj(i -> List.of(new KeptWays.Keep(i, true))).toList(), elements);
    }

    private static Proposition.WaysToWrite waysOf(List<LinearForm<Quantity>> forms,
                                                  Proposition reading) {
        Map<Integer, Proposition> conditions = new HashMap<>();
        for (int i = 0; i < forms.size(); i++) {
            conditions.put(i, truth("t" + i));
        }
        return new Proposition.WaysToWrite(eachKeptByItsOwnTruth(forms.size()), conditions,
                reading, forms, SUM, Optional.empty(), 0, false, Optional.empty(), 0,
                2 * (1L << forms.size()) - 1);
    }

    /** The numbers of the parts nothing read that stand in {@code stated}. */
    private static void numbersIn(Proposition stated, Set<Integer> into) {
        if (stated instanceof Proposition.Unread unread) {
            into.add(unread.ordinal());
        }
        stated.partsHeld().forEach(each -> numbersIn(each, into));
    }

    private static List<LinearForm<Quantity>> ones(int elements) {
        List<LinearForm<Quantity>> forms = new ArrayList<>();
        for (int i = 0; i < elements; i++) {
            forms.add(LinearForm.constant(ExactRatio.ONE));
        }
        return forms;
    }

    /** The derivation of ways that all state alike, whatever each keeps. */
    private static Derivation.WaysWrittenWhenAsked alike(int elements) {
        Map<Integer, Derivation> conditions = new HashMap<>();
        for (int i = 0; i < elements; i++) {
            conditions.put(i, new Derivation.ATruthOfASubject(
                    new DecisionSubject.AnInput(TermPath.of("t" + i)), true));
        }
        return new Derivation.WaysWrittenWhenAsked(eachKeptByItsOwnTruth(elements), conditions,
                new Derivation.ACutThatCutsNothing(true, Set.of()), ones(elements), SUM,
                Optional.empty(), 0, Map.of(), false);
    }

    @Test
    void holdingDenyingAndComparingItWriteNothingOut() {
        Proposition.OfTheWays ways = WaysSamples.over(truth("a"));
        assertEquals(ways, ways.denied().denied());
        assertNotEquals(ways, ways.denied());
        assertEquals(ways, WaysSamples.over(truth("a")));
        assertNotEquals(ways, WaysSamples.over(truth("b")));
    }

    @Test
    void itsCasesAreWrittenOutOnceHoweverOftenAndWhicheverWayRoundItIsAsked() {
        Proposition.OfTheWays ways = WaysSamples.over(truth("a"));
        assertSame(ways.written(), ways.written());
        assertEquals(ways.written().denied(), ((Proposition.OfTheWays) ways.denied()).written());
    }

    @Test
    void waysThatAllStateAlikeAreReadHoweverManyTheyAreWithinTheWorkThatIsDone() {
        // 2^13 ways: past what a statement may come to if each way were a case of its own, and
        // one condition after another where they all state alike.
        Proposition stated = new Conclusion(Optional.empty()).of(alike(13));
        Proposition.OfTheWays ways = assertInstanceOf(Proposition.OfTheWays.class, stated);
        assertNull(Proposition.firstStopIn(ways),
                "the cases come to few parts however many ways there are");
    }

    @Test
    void waysPastTheWorkThatIsDoneAreAPartNothingReadAndSayWhy() {
        Proposition stated = new Conclusion(Optional.empty()).of(alike(15));
        assertInstanceOf(WhyUnread.MoreWaysThanAreWrittenOut.class,
                Proposition.firstStopIn(stated));
    }

    @Test
    void thePartsNothingReadInTheCasesAreNumberedWithinWhatTheStatementWasOwed() {
        // Every way that keeps both of the first two cannot hold its total: half of the ways, and
        // the steps that join them are numbered beside, from the same numbers.
        List<LinearForm<Quantity>> forms = ones(7);
        LinearForm<Quantity> greatest = LinearForm.constant(ExactRatio.tenTo(Long.MAX_VALUE));
        forms.set(0, greatest);
        forms.set(1, greatest);
        Proposition.WaysToWrite ways = waysOf(forms, totalAtLeastOne());
        Set<Integer> numbers = new TreeSet<>();
        numbersIn(new Proposition.OfTheWays(ways, true).written(), numbers);
        assertTrue(numbers.size() > 1);
        assertTrue(numbers.stream().allMatch(number -> number >= ways.firstNumber()
                && number < ways.firstNumber() + ways.numbersOwed()), () -> "numbered " + numbers);
    }

    @Test
    void aStatementOverManyWaysIsOwedNumbersForEveryWayAndEveryStepThatJoinsTwo() {
        Conclusion concluding = new Conclusion(Optional.empty());
        Proposition.OfTheWays ways = assertInstanceOf(Proposition.OfTheWays.class,
                concluding.of(alike(13)));
        Proposition beside = concluding.of(new Derivation.Stopped(new WhyUnread.NotArithmetic(),
                false));
        // 2^13 ways and one fewer steps that join two of them.
        assertEquals((1 << 14) - 1, ((Proposition.Unread) beside).ordinal(),
                "a part concluded beside the statement is numbered after all it is owed");
        assertEquals((1 << 14) - 1, ways.ways().numbersOwed());
    }

    @Test
    void aNumberOfSomeWaysThatNoNumberHoldsIsFoundWhereTheCasesAreWritten() {
        List<LinearForm<Quantity>> forms = ones(7);
        LinearForm<Quantity> greatest = LinearForm.constant(ExactRatio.tenTo(Long.MAX_VALUE));
        forms.set(0, greatest);
        forms.set(1, greatest);
        Proposition.OfTheWays ways = new Proposition.OfTheWays(
                waysOf(forms, totalAtLeastOne()), true);
        assertInstanceOf(WhyUnread.ANumberNotHeld.class, Proposition.firstStopIn(ways),
                "only the ways that keep both are owed one, and they are found without asking"
                        + " for the cases");
        assertTrue(Proposition.stopsIn(ways).size() > 1,
                "each way that keeps both is a part nothing read");
        assertNull(Proposition.firstStopIn(new Proposition.OfTheWays(
                waysOf(ones(7), totalAtLeastOne()), true)));
    }
}
