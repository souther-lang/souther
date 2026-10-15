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
