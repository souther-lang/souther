package souther.compiler.reading;

import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.ElementsWrittenOut;
import souther.compiler.check.ScopeStep;
import souther.compiler.core.Core;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.InputReads;

import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
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
         * @param viaNames whether it was found beneath a name that stands for something written
         *                 elsewhere, rather than in the value itself or under its own lets
         */
        record OneComparison(Core.Binary comparison, InputReads at, boolean viaNames)
                implements Of { }

        /**
         * Forks this does not read, every one that decides the value: a value that comes to a sum
         * of two choices is decided by two, and is not one choice whichever is met first.
         *
         * @param origins the forks, each once however often it is reached
         */
        record Unread(List<Origin> origins) implements Of {

            public Unread {
                origins = List.copyOf(origins);
            }
        }
    }

    /**
     * One fork that decides a value, or the place a walk gave up.
     *
     * @param fork     the expression the fork is, which two values that are the one choice have in
     *                 common; null where the walk followed names too far to reach one
     * @param viaNames whether it was found beneath a name that stands for something written
     *                 elsewhere, as in {@link Of.OneComparison}
     * @param perApplication whether the fork is written where an application of a closure is on, so
     *                 that it is made again on each application whatever it reads: a fork held in
     *                 a name is one choice when it is not
     */
    record Origin(Core fork, boolean viaNames, boolean perApplication) { }

    /** A value followed to what it comes to, and the reading its names are read in there. */
    private record Comes(Core core, InputReads at, boolean viaNames) { }

    /** What decides {@code value}, followed to what it comes to by {@code names}. */
    static Of of(Denotation value, ElementsWrittenOut.Reading<InputReads> names,
                 DeclarationNewtypes newtypes) {
        Comes comes = followed(value, names, newtypes);
        if (comes == null) {
            return new Of.Unread(List.of(new Origin(null, true, true)));
        }
        if (Core.withoutStanding(comes.core()) instanceof Core.If fork
                && Core.withoutStanding(fork.cond()) instanceof Core.Binary comparison
                && !comparison.op().stopsWhenItsAnswerIsSettled()
                && !decides(fork.cond(), comes.at(), names, newtypes, 0, newSeen())
                && !decides(fork.then(), comes.at(), names, newtypes, 0, newSeen())
                && !decides(fork.els(), comes.at(), names, newtypes, 0, newSeen())) {
            return new Of.OneComparison(comparison, comes.at(), comes.viaNames());
        }
        List<Fork> found = new ArrayList<>();
        forksIn(comes.core(), comes.at(), names, newtypes, 0, newSeen(), found);
        if (found.isEmpty()) {
            return new Of.Fixed();
        }
        // The fork itself is what the choice is, and a fork held in a name is made where the name
        // was written, whichever expression handed it on.
        List<Origin> origins = new ArrayList<>();
        for (Fork each : found) {
            boolean perApplication = each.throughAName() ? each.perApplication()
                    : each.fork() == null || comes.at().isOnAnApplication();
            origins.add(new Origin(each.fork(), comes.viaNames() || each.throughAName(),
                    perApplication));
        }
        return new Of.Unread(origins);
    }

    /** {@code value} under its {@code let}s and past the names that stand for something else, or
     *  null where that is more steps than are taken. */
    private static Comes followed(Denotation value, ElementsWrittenOut.Reading<InputReads> names,
                                  DeclarationNewtypes newtypes) {
        Core e = value.value();
        InputReads at = value.at();
        boolean viaNames = false;
        // The values of the lets this walk went under: a name that stands for one of them was
        // written in the value itself, and is evaluated where the value is.
        Set<Core> writtenHere = newSeen();
        for (int steps = 0; steps < MOST_STEPS; steps++) {
            if (Core.withoutStanding(e) instanceof Core.LetIn let) {
                writtenHere.add(Core.withoutStanding(let.value()));
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
                viaNames = viaNames || !writtenHere.contains(Core.withoutStanding(e));
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
                                   ElementsWrittenOut.Reading<InputReads> names,
                                   DeclarationNewtypes newtypes, int steps,
                                   Set<Core> seen) {
        List<Fork> found = new ArrayList<>();
        forksIn(e, at, names, newtypes, steps, seen, found);
        return !found.isEmpty();
    }

    /** A fork found in a value, whether it was found beneath a name, and whether the name nearest
     *  it turns on an application. The fork is null where the walk went too far to say which it
     *  was. */
    private record Fork(Core fork, boolean throughAName, boolean perApplication) { }

    /**
     * Every fork in {@code e}, through the names it reads, each once: a fork holds more forks in
     * its condition and its arms, a value made of several parts holds the forks of each, and a name
     * used twice stands for one.
     */
    private static void forksIn(Core e, InputReads at,
                                ElementsWrittenOut.Reading<InputReads> names,
                                DeclarationNewtypes newtypes, int steps, Set<Core> seen,
                                List<Fork> out) {
        switch (Core.withoutStanding(e)) {
            case Core.If _, Core.Match _, Core.IfConstructed _ -> {
                out.add(new Fork(Core.withoutStanding(e), false, false));
                forksInParts(e, at, names, newtypes, steps, seen, out);
            }
            case Core.Read read -> forksStoodFor(read, at, names, newtypes, steps, seen, out);
            default -> forksInParts(e, at, names, newtypes, steps, seen, out);
        }
    }

    /** Every fork in what a name stands for. */
    private static void forksStoodFor(Core.Read read, InputReads at,
                                      ElementsWrittenOut.Reading<InputReads> names,
                                      DeclarationNewtypes newtypes, int steps, Set<Core> seen,
                                      List<Fork> out) {
        if (steps >= MOST_STEPS) {
            out.add(new Fork(null, true, true));
            return;
        }
        ElementsWrittenOut.Stood<InputReads> stands = names.standing(read, at);
        Core there = Core.withoutStanding(stands.value());
        // A name that stands for itself is a position of the input, and decides nothing.
        if (there == read || !seen.add(there)) {
            return;
        }
        List<Fork> inner = new ArrayList<>();
        forksIn(there, stands.at(), names, newtypes, steps + 1, seen, inner);
        // Whether a fork is made again on each application is a fact about the fork, read where
        // it was written, and the name nearest it is the one to have said so.
        for (Fork found : inner) {
            out.add(new Fork(found.fork(), true, found.throughAName() ? found.perApplication()
                    : found.fork() == null || stands.at().isOnAnApplication()));
        }
    }

    /** Every fork in any part of {@code e}. */
    private static void forksInParts(Core e, InputReads at,
                                     ElementsWrittenOut.Reading<InputReads> names,
                                     DeclarationNewtypes newtypes, int steps, Set<Core> seen,
                                     List<Fork> out) {
        Core.forEachChild(e, child -> forksIn(child, at, names, newtypes, steps, seen, out));
    }
}
