package souther.compiler.check;

import souther.compiler.Compiler;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A case split a value is handed is read inside every binder it stands in, and what it hands the
 * expression it stands in is read where that expression stands.
 *
 * <p>The two are not the same place. What the split asks is walked under the binders — an attempt's
 * success branch, a {@code let}'s body — because that is where it is written and what it names is
 * named there. A continuation is outside them, and a state settled inside a binder says things
 * about a place a continuation cannot see. Handing it on says those things hold out there.
 *
 * <p>Nothing downstream reads them either way, which is why no diagnostic states this. The facts
 * that differ are about the binders themselves: an attempt seeds what it built under the binding it
 * opened, and a caller outside cannot name that binding, so a construction out there is discharged
 * by neither state. What is wrong with handing it on is that it is a state read somewhere else, and
 * the next fact filed under a term the caller <em>can</em> name would be handed out with it.
 *
 * <p>So it is read off {@link InvariantChecker#CARRIED}. Two things are held here and the first is
 * that the second is about something: that a split really does stand inside binders — the search
 * lifts one out of an attempt's success branch ({@link InvariantChecker.SplitSite}) — and that a
 * corpus which happens not to contain one says nothing about whether it can.
 */
class ASplitStandingInsideBindersHandsOnWhatTheCallerCanReadTest {

    /**
     * A helper holding an attempted construction and, after it, an {@code if} handed as a value.
     *
     * <p>A helper because that is what puts the attempt inside a value: the call is written out as
     * the helper's body where the call stood, so the attempt stands in a field of the construction
     * below. Written at the top of a behavior's own body the attempt is the body, and the search
     * that lifts a split never descends into it from anywhere.
     */
    private static final String MODULE = """
            module demo

            data Pos = Int
                invariant value > 0

            data Nat = Int
                invariant value >= 0

            data Rejected
            data Held = { p: Pos, n: Nat }

            let pick (k: Int, x: Int): Pos = {
                guard Pos(k) as p else Pos(1)
                if x > 1 then p else p
            }

            behavior take : (k: Int, x: Int) -> Held | Rejected
                constructs Held, Pos, Nat
            let take (k, x) = Held { p = pick(k, x), n = Nat(k) }
            """;

    /** Every split the check opened while compiling {@code module}. */
    private static List<InvariantChecker.Carried> openedIn(String module) {
        List<InvariantChecker.Carried> carried = new ArrayList<>();
        InvariantChecker.CARRIED = carried;
        try {
            Compiler.compileWithWarnings(module);
        } finally {
            InvariantChecker.CARRIED = null;
        }
        return List.copyOf(carried);
    }

    @Test
    void aSplitIsOpenedInsideBindersAndHandsOnTheStateOutsideThem() {
        List<InvariantChecker.Carried> opened = openedIn(MODULE);

        List<InvariantChecker.Carried> inside =
                opened.stream().filter(one -> one.binders() > 0).toList();
        assertTrue(!inside.isEmpty(),
                "a split standing inside binders is a thing this compiler opens, and this is one —"
                        + " opened " + opened.size() + " splits, none of them inside anything");

        assertEquals(List.of(), inside.stream()
                        .filter(InvariantChecker.Carried::handedOnWhatWasReadInside).toList(),
                "and none of them hands on the state it was read under, which is stated where the"
                        + " expression it stands in is not");
    }

    /**
     * The control for the second half: a split standing inside nothing is read where its expression
     * stands, so what it hands on is what it found. Read as one rule — the state comes out where it
     * was read where the continuation stands — this is the same rule answering the other way, and a
     * reading that always handed on what stood before the split would pass the assertion above
     * while saying nothing.
     */
    @Test
    void aSplitInsideNothingHandsOnWhatItFound() {
        List<InvariantChecker.Carried> opened = openedIn("""
                module demo

                data Nat = Int
                    invariant value >= 0

                data Bad

                behavior take : (k: Int, x: Int) -> Nat | Bad
                    constructs Nat
                let take (k, x) = Nat(if x > 1 then k else k)
                """);

        assertEquals(List.of(), opened.stream().filter(one -> one.binders() > 0).toList(),
                "nothing stands over this one");
        assertTrue(opened.stream().allMatch(InvariantChecker.Carried::handedOnWhatWasReadInside),
                "so where it was read and where it stands are one place, and what it found comes"
                        + " out — opened " + opened.size() + " splits");
    }
}
