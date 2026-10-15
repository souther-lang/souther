package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a line read on several applications decides is each case of where it decides on one of
 * them, met where that application is made — said one by one while they are few, and as one past
 * that, standing for each of them.
 *
 * <p>The same cases either way. Said as one, a row on one side of the line may be at one
 * application's case and the row on the other side at another's, and the line turns nothing
 * between those; so what the one is said for is kept, for a reader asking each of them.
 */
class ALineReadOnManyApplicationsStandsForEachCaseOfEachTest {

    private static Proposition truth(String at) {
        return new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of(at)), true);
    }

    /** {@code applications} applications, each made under a truth of its own and deciding under
     *  another. */
    private static List<WhereAnApplicationIsMade.OnOne> readings(int applications) {
        List<WhereAnApplicationIsMade.OnOne> out = new ArrayList<>();
        for (int i = 0; i < applications; i++) {
            out.add(new WhereAnApplicationIsMade.OnOne(
                    List.of(DecidingCase.alone(truth("d" + i))), truth("r" + i)));
        }
        return out;
    }

    /** Each case of each application, met where it is made. */
    private static Set<Proposition> met(int applications) {
        List<Proposition> out = new ArrayList<>();
        for (int i = 0; i < applications; i++) {
            out.add(Proposition.all(List.of(truth("d" + i), truth("r" + i))));
        }
        return Set.copyOf(out);
    }

    private static final Proposition A = truth("a");
    private static final Proposition B = truth("b");
    private static final Proposition C = truth("c");
    private static final Proposition D = truth("d");

    /** One application, made wherever a row is, deciding in {@code cases}. */
    private static WhereAnApplicationIsMade.OnOne madeEverywhere(DecidingCase... cases) {
        return new WhereAnApplicationIsMade.OnOne(List.of(cases), new Proposition.Always(true));
    }

    /**
     * Two applications deciding under one condition, one where it is a case of its own and one
     * where it was said for two: what the two decide in is one case, the condition, whichever is
     * read first. Rows on both sides of the line in {@code a} or in {@code b} are rows on both
     * sides of it in {@code a || b}, which is a case of its own.
     */
    @Test
    void oneConditionSaidAloneAndForTwoIsTheConditionAloneInEitherOrder() {
        DecidingCase split = DecidingCase.someOneOf(List.of(DecidingCase.alone(A),
                DecidingCase.alone(B)));
        DecidingCase whole = DecidingCase.alone(Proposition.any(List.of(A, B)));

        List<DecidingCase> first = WhereAnApplicationIsMade.decidesOn(
                List.of(madeEverywhere(split), madeEverywhere(whole)));
        List<DecidingCase> second = WhereAnApplicationIsMade.decidesOn(
                List.of(madeEverywhere(whole), madeEverywhere(split)));

        assertEquals(List.of(whole), first, "the condition, standing for itself");
        assertEquals(first, second, "whichever application is read first");
    }

    /**
     * And one condition said for two different pairs of cases stands for every case of both,
     * whichever is read first: a line deciding in a case of either is one rows divide there.
     */
    @Test
    void oneConditionSaidForTwoWaysOfCasesStandsForEveryCaseOfBoth() {
        Proposition either = Proposition.any(List.of(A, B, Proposition.all(List.of(C, D))));
        DecidingCase byA = new DecidingCase(either, new DecidingCase.Cases.EachOf(List.of(
                new DecidingCase.Cases.One(A),
                new DecidingCase.Cases.One(Proposition.any(List.of(B,
                        Proposition.all(List.of(C, D))))))));
        DecidingCase byB = new DecidingCase(either, new DecidingCase.Cases.EachOf(List.of(
                new DecidingCase.Cases.One(B),
                new DecidingCase.Cases.One(Proposition.any(List.of(A,
                        Proposition.all(List.of(C, D))))))));

        for (List<DecidingCase> order : List.of(List.of(byA, byB), List.of(byB, byA))) {
            List<DecidingCase> cases = WhereAnApplicationIsMade.decidesOn(order.stream()
                    .map(ALineReadOnManyApplicationsStandsForEachCaseOfEachTest::madeEverywhere)
                    .toList());
            assertEquals(1, cases.size(), () -> "one condition: " + cases);
            assertEquals(Set.of(A, B,
                            Proposition.any(List.of(B, Proposition.all(List.of(C, D)))),
                            Proposition.any(List.of(A, Proposition.all(List.of(C, D))))),
                    Set.copyOf(DecidingCases.eachOf(cases.getFirst().standsFor())),
                    () -> "every case of both, read in the order " + order);
        }
    }

    /**
     * A condition holding wherever a row is, said for several cases, is not a line deciding
     * wherever a row is: neither the cases of another application nor the several it stands for
     * are said nothing more by it.
     */
    @Test
    void aConditionHoldingEverywhereSaidForSeveralIsNoLineDecidingEverywhere() {
        DecidingCase everywhereForTwo = new DecidingCase(new Proposition.Always(true),
                new DecidingCase.Cases.EachOf(List.of(new DecidingCase.Cases.One(A),
                        new DecidingCase.Cases.One(A.denied()))));

        assertTrue(!WhereAnApplicationIsMade.everywhere(List.of(everywhereForTwo)),
                "it decides only where rows on both sides are in one of the two");
        assertEquals(List.of(everywhereForTwo, DecidingCase.alone(C)),
                WhereAnApplicationIsMade.decidesOn(List.of(madeEverywhere(everywhereForTwo),
                        madeEverywhere(DecidingCase.alone(C)))),
                "and the other application's case is still one of its own");
    }

    @Test
    void asManyAsAreSaidOneByOneAreEachTheirOwn() {
        int most = WhereEachLineDecides.MOST_CASES;
        List<DecidingCase> cases = WhereAnApplicationIsMade.decidesOn(readings(most));

        assertEquals(met(most), Set.copyOf(cases.stream().map(DecidingCase::condition).toList()));
        assertTrue(cases.stream().allMatch(DecidingCase::saidAlone),
                () -> "each said for itself alone: " + cases);
    }

    @Test
    void oneMoreAreSaidAsOneStandingForEachOfThem() {
        int more = WhereEachLineDecides.MOST_CASES + 1;
        List<DecidingCase> cases = WhereAnApplicationIsMade.decidesOn(readings(more));

        assertEquals(1, cases.size(), () -> "said as one: " + cases);
        assertEquals(Proposition.any(List.copyOf(met(more))), cases.getFirst().condition(),
                "some one of them holding");
        assertEquals(met(more), Set.copyOf(DecidingCases.eachOf(cases.getFirst().standsFor())),
                "and standing for each case of each application, met where it is made");
    }
}
