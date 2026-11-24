package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.DeclaredInput;
import souther.compiler.inputs.InputReads;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.WhyUnread;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Of the applications a run may make of a closure, the ones read in turn
 * ({@link StopsOfABody#madeInTurn}): each made wherever the ones before it are got past, without
 * those made on no run, up to and with the first made only on some rows.
 */
class TheApplicationsARunMakesInTurnStopAtTheFirstMadeOnlyOnSomeRowsTest {

    private static final Proposition EVERY_ROW = new Proposition.Always(true);
    private static final Proposition NO_ROW = new Proposition.Always(false);
    private static final Proposition SOME_ROWS = new Proposition.Unread(Optional.empty(), 0,
            new WhyUnread.WhichElementARunStopsAt(), false, true);

    /** The {@code place}-th application, made where {@code made} holds. */
    private static ClosureApplications.Application made(int place, Proposition made) {
        return new ClosureApplications.Application(
                InputReads.ofWhatIsDeclared(Map.of(), DeclaredInput.NONE), made, Map.of(),
                ElementsMetOn.EVERY, List.of(), List.of(place),
                ClosureApplications.MadeOnEvery.NOT_SHOWN, List.of(), Optional.of(made));
    }

    /** The places of what is read in turn of applications made where each of {@code made}
     *  holds, in that order. */
    private static List<Integer> inTurn(Proposition... made) {
        List<ClosureApplications.Application> applications = new ArrayList<>();
        for (int place = 0; place < made.length; place++) {
            applications.add(made(place, made[place]));
        }
        return StopsOfABody.madeInTurn(applications).stream()
                .map(one -> one.places().getFirst()).toList();
    }

    @Test
    void eachIsReadInTurnUpToAndWithTheFirstMadeOnlyOnSomeRows() {
        assertEquals(List.of(0, 1, 2), inTurn(EVERY_ROW, EVERY_ROW, EVERY_ROW));
        assertEquals(List.of(0, 2), inTurn(EVERY_ROW, NO_ROW, EVERY_ROW));
        assertEquals(List.of(0), inTurn(SOME_ROWS, EVERY_ROW));
        assertEquals(List.of(0, 1), inTurn(EVERY_ROW, SOME_ROWS, EVERY_ROW));
        assertEquals(List.of(1), inTurn(NO_ROW, SOME_ROWS, EVERY_ROW));
    }
}
