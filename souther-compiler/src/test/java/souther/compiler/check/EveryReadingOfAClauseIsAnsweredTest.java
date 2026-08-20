package souther.compiler.check;

import souther.compiler.diag.SourcePos;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A clause read more than one way is answered more than one way.
 *
 * <p>What is written as one thing need not be read as one thing: a clause naming a helper is one
 * thing to its author and is whatever that helper states to the check, and its parts can be read
 * differently. Answered with one of the readings, an author is told what discharges half of their
 * clause and left to find out about the other half from a construction that is still refused.
 *
 * <p>Held here rather than through a program, because no program takes these shapes today — a clause
 * that names a helper is read as one term and states one thing to the check. It is the day the check
 * reads further into what a clause names that a clause states two of these at once, and a mechanism
 * whose data never takes a shape it is written for is a mechanism nothing has run.
 */
class EveryReadingOfAClauseIsAnsweredTest {

    private static final SourcePos AT = new SourcePos(3, 5);

    private static List<ClauseDischarge.Kind> kinds(boolean asABound, boolean asATerm,
                                                    boolean unread) {
        List<ClauseDischarge.Kind> out = new ArrayList<>();
        for (ClauseDischarge each
                : ClauseDischarge.readings(asABound, asATerm, unread, AT, () -> "why")) {
            assertEquals(AT, each.clause(), "every reading is of the clause that was read");
            out.add(each.kind());
        }
        return out;
    }

    @Test
    void aClauseReadOneWayIsAnsweredOnce() {
        assertEquals(List.of(ClauseDischarge.Kind.DERIVABLE), kinds(true, false, false));
        assertEquals(List.of(ClauseDischarge.Kind.EXACT_MATCH), kinds(false, true, false));
    }

    /** The reason a single answer is wrong: neither reading describes the other's half, and which of
     *  them a reader is handed decides what they believe a guard will do. */
    @Test
    void aClauseReadAsABoundAndAsATermIsAnsweredAsBoth() {
        assertEquals(List.of(ClauseDischarge.Kind.DERIVABLE, ClauseDischarge.Kind.EXACT_MATCH),
                kinds(true, true, false));
    }

    /**
     * What was not read is said even where something else was.
     *
     * <p>This is the one that decides a program: a clause part of which is outside the fragment is a
     * clause no guard discharges, and answering it by the part that was read tells an author their
     * construction can be judged safe when it cannot.
     */
    @Test
    void whatWasNotReadIsSaidBesideWhatWas() {
        assertTrue(kinds(true, false, true).contains(ClauseDischarge.Kind.RUNTIME_ONLY),
                "a bound and a part nothing was made of");
        assertTrue(kinds(false, true, true).contains(ClauseDischarge.Kind.RUNTIME_ONLY),
                "a term and a part nothing was made of");
        assertTrue(kinds(true, true, true).contains(ClauseDischarge.Kind.RUNTIME_ONLY));
    }

    @Test
    void aClauseNothingWasMadeOfIsAnsweredOnce() {
        assertEquals(List.of(ClauseDischarge.Kind.RUNTIME_ONLY), kinds(false, false, true));
        assertEquals(List.of(ClauseDischarge.Kind.RUNTIME_ONLY), kinds(false, false, false));
    }

    /** The reason is what an author acts on, and it is only asked for where there is something to
     *  say — reading a clause to find out what it is missing costs a walk of it. */
    @Test
    void whyIsAskedOnlyWhereSomethingWasNotRead() {
        boolean[] asked = {false};
        ClauseDischarge.readings(true, false, false, AT, () -> {
            asked[0] = true;
            return "why";
        });
        assertTrue(!asked[0], "nothing was left unread, so there is nothing to explain");

        ClauseDischarge.readings(true, false, true, AT, () -> {
            asked[0] = true;
            return "why";
        });
        assertTrue(asked[0], "and it is asked where there is");
    }
}
