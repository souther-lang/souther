package souther.compiler.reading;

import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.ElementsWrittenOut;
import souther.compiler.check.ScopeStep;
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
 * <p>Read to what the value is, through the {@code let}s it is written under and the names it is
 * written with. An element handed to a closure is a name in the closure's body, and the choice it
 * makes may be in what the name stands for rather than in the body — the closure {@code x -> x}
 * answers whatever it was handed, and the choice is in the list it was handed it from. A walk that
 * stopped at the names would read that value as deciding nothing, which is the one answer this must
 * never give about a value it did not read to the end.
 *
 * <p>Read as one comparison only where what the value comes to is an {@code if} on a comparison and
 * nothing is decided beneath it. Anything else that holds a fork is a decision this does not read,
 * and says so. And whether the choice was found through a name is said, because it is the one thing
 * that tells whether the closure the value was made by is the closure the choice is evaluated in:
 * what a name stands for was evaluated where it was written, which may be another closure than the
 * one that answered it.
 */
final class ValueChoices {

    /** How far a value may be followed to what it comes to before it is called unread. */
    private static final int MOST_STEPS = 8;

    private ValueChoices() {
    }

    /** What decides a value. */
    sealed interface Of {

        /** Nothing: the value is what it is however a run goes. */
        record Fixed() implements Of { }

        /**
         * An {@code if} on one comparison, read where the names are, with nothing decided in either
         * branch.
         *
         * @param viaNames whether it was found beneath a name rather than in the value itself
         */
        record OneComparison(Core.Binary comparison, InputReads at, boolean viaNames)
                implements Of { }

        /** A fork this does not read, or one it followed names too far to find the end of. */
        record Unread() implements Of { }
    }

    /** A value followed to what it comes to, and the reading its names are read in there. */
    private record Comes(Core core, InputReads at, boolean viaNames) { }

    /** What decides {@code value}, followed to what it comes to by {@code names}. */
    static Of of(Denotation value, ElementsWrittenOut.Reading<InputReads> names,
                 DeclarationNewtypes newtypes) {
        Comes comes = followed(value, names, newtypes);
        if (comes == null) {
            return new Of.Unread();
        }
        if (Core.withoutStanding(comes.core()) instanceof Core.If fork
                && Core.withoutStanding(fork.cond()) instanceof Core.Binary comparison
                && !comparison.op().stopsWhenItsAnswerIsSettled()
                && !decides(fork.cond(), comes.at(), names, 0, newSeen())
                && !decides(fork.then(), comes.at(), names, 0, newSeen())
                && !decides(fork.els(), comes.at(), names, 0, newSeen())) {
            return new Of.OneComparison(comparison, comes.at(), comes.viaNames());
        }
        return decides(comes.core(), comes.at(), names, 0, newSeen()) ? new Of.Unread()
                : new Of.Fixed();
    }

    /** {@code value} under its {@code let}s and past the names that stand for something else, or
     *  null where that is more steps than are taken. */
    private static Comes followed(Denotation value, ElementsWrittenOut.Reading<InputReads> names,
                                  DeclarationNewtypes newtypes) {
        Core e = value.value();
        InputReads at = value.at();
        boolean viaNames = false;
        for (int steps = 0; steps < MOST_STEPS; steps++) {
            if (Core.withoutStanding(e) instanceof Core.LetIn let) {
                at = at.entering(new ScopeStep.Let(let), names.symbols(), newtypes);
                e = let.body();
            } else if (Core.withoutStanding(e) instanceof Core.Read read) {
                ElementsWrittenOut.Stood<InputReads> stands = names.standing(read, at);
                // A name that stands for itself is a position of the input, and is where it ends.
                if (Core.withoutStanding(stands.value()) == read) {
                    return new Comes(read, at, viaNames);
                }
                e = stands.value();
                at = stands.at();
                viaNames = true;
            } else {
                return new Comes(e, at, viaNames);
            }
        }
        return null;
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
