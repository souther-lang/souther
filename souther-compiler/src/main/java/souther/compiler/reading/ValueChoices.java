package souther.compiler.reading;

import souther.compiler.check.ElementsWrittenOut;
import souther.compiler.core.Core;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.InputReads;

import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Set;

/**
 * What decides the value an element is worth, as against whether the element is there.
 *
 * <p>A total is a function of both. {@code List.sum(List.map(r -> if r.days >= 17 then r.pay else
 * 0, [a, b]))} keeps every element and decides what each is worth, and is the same sum of two
 * choices that {@code (if a.days >= 17 then a.pay else 0) + (if b.days >= 17 then b.pay else 0)}
 * is. Which elements are there is {@link ElementEvaluations}' to read off what keeps them; this reads
 * the other half off the value each is.
 *
 * <p>Followed through the names the value is written with, to what they stand for. An element handed
 * to a closure is a name in the closure's body, and the choice it makes may be in what the name
 * stands for rather than in the body: a value that reads as plain arithmetic of a name can hold a
 * fork one step further in. A walk that stopped at the names would read that value as deciding
 * nothing, which is the one answer this must never give about a value it did not read to the end.
 *
 * <p>Read as one comparison only where the value is an {@code if} on a comparison of an input and
 * nothing is decided beneath it. Anything else that holds a fork is a decision this does not read,
 * and says so.
 */
final class ValueChoices {

    /** How far a name may be followed to what it stands for before the value is called unread. */
    private static final int MOST_STEPS = 8;

    private ValueChoices() {
    }

    /** What decides a value. */
    sealed interface Of {

        /** Nothing: the value is what it is however a run goes. */
        record Fixed() implements Of { }

        /** An {@code if} on one comparison, read where the names are, with nothing decided in
         *  either branch. */
        record OneComparison(Core.Binary comparison, InputReads at) implements Of { }

        /** A fork this does not read, or one it followed names too far to find the end of. */
        record Unread() implements Of { }
    }

    /** What decides {@code value}, its names followed by {@code names}. */
    static Of of(Denotation value, ElementsWrittenOut.Reading<InputReads> names) {
        if (Core.withoutStanding(value.value()) instanceof Core.If fork
                && Core.withoutStanding(fork.cond()) instanceof Core.Binary comparison
                && !comparison.op().stopsWhenItsAnswerIsSettled()
                && !decides(fork.cond(), value.at(), names, 0, newSeen())
                && !decides(fork.then(), value.at(), names, 0, newSeen())
                && !decides(fork.els(), value.at(), names, 0, newSeen())) {
            return new Of.OneComparison(comparison, value.at());
        }
        return decides(value.value(), value.at(), names, 0, newSeen()) ? new Of.Unread()
                : new Of.Fixed();
    }

    private static Set<Core> newSeen() {
        return Collections.newSetFromMap(new IdentityHashMap<>());
    }

    /** Whether anything in {@code e} is a fork, through the names it reads. */
    private static boolean decides(Core e, InputReads at,
                                   ElementsWrittenOut.Reading<InputReads> names, int steps,
                                   Set<Core> seen) {
        return switch (Core.withoutStanding(e)) {
            case Core.If _, Core.Match _, Core.IfConstructed _ -> true;
            case Core.Read read -> stoodForDecides(read, at, names, steps, seen);
            default -> anyPartDecides(e, at, names, steps, seen);
        };
    }

    /** Whether what a name stands for is, or holds, a fork. */
    private static boolean stoodForDecides(Core.Read read, InputReads at,
                                           ElementsWrittenOut.Reading<InputReads> names,
                                           int steps, Set<Core> seen) {
        if (steps >= MOST_STEPS) {
            return true;
        }
        ElementsWrittenOut.Stood<InputReads> stands = names.standing(read, at);
        Core there = Core.withoutStanding(stands.value());
        // A name that stands for itself is a position of the input, and decides nothing.
        if (there == read || !seen.add(there)) {
            return false;
        }
        return decides(there, stands.at(), names, steps + 1, seen);
    }

    /** Whether any part of {@code e} is, or holds, a fork. */
    private static boolean anyPartDecides(Core e, InputReads at,
                                          ElementsWrittenOut.Reading<InputReads> names,
                                          int steps, Set<Core> seen) {
        boolean[] found = {false};
        Core.forEachChild(e, child -> {
            if (!found[0] && decides(child, at, names, steps, seen)) {
                found[0] = true;
            }
        });
        return found[0];
    }
}
