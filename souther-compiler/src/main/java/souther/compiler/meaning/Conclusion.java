package souther.compiler.meaning;

import souther.compiler.partition.CompositionBudget;
import souther.compiler.types.ModelOccurrence;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * One concluding of a derivation: what each of its steps comes to, with the parts nothing read
 * numbered in the order they are met.
 *
 * <p>The numbers are given here and not where the reading stopped. A reading may try more than one
 * rule at a place and keep one, and a part a rule it did not keep stopped at was never part of what
 * is stated — numbered as it was met, it would move the number of every part after it.
 *
 * <p>Kept by step, by identity, because a step and its conclusion are what a reader of where each
 * part was read off asks about: two steps alike in every component are still two places in the
 * condition.
 *
 * <p><b>And under what it supposes of the values walks carried.</b> A walk's step is read once,
 * with what the walk carried into it standing as itself, and concluded once for each way that
 * value is supposed to have come out ({@link #supposing}). A step that never reads a carried value
 * concludes the same under every supposition, so it is concluded once for all of them: what is
 * kept of a step is the suppositions it read, and it is taken again wherever those are the same.
 * Concluded where nothing supposes it, a carried value is itself ({@link Proposition.Carried}): a
 * part read, which a walk deciding how it closes takes either way.
 */
public final class Conclusion {

    /**
     * How many parts a step is concluded with
     * ({@link CompositionBudget#PARTS_A_DERIVATION_CONCLUDES}), read here and nowhere else.
     */
    private static final CompositionBudget PARTS = CompositionBudget.PARTS_A_DERIVATION_CONCLUDES;

    /** What every concluding made from one by supposing more shares: where, the numbering, and
     *  what each step came to. */
    private static final class Shared {
        private final Optional<ModelOccurrence> where;
        private final boolean reusing;
        private final Map<Derivation, List<Kept>> kept = new IdentityHashMap<>();
        private final Map<Derivation, Proposition> last = new IdentityHashMap<>();
        /** The carried values each step being concluded has read so far, innermost last. */
        private final Deque<Set<ACarriedValue>> reading = new ArrayDeque<>();
        /** How many parts each statement concluded here comes to written out, past the figure
         *  held at one past it. By identity, since a part held twice is one statement counted
         *  twice wherever it is held. */
        private final Map<Proposition, Long> parts = new IdentityHashMap<>();
        /** The figure parts are counted up to, and held at one past. */
        private final long mostParts;
        private int unread;

        private Shared(Optional<ModelOccurrence> where, boolean reusing) {
            this(where, reusing, PARTS);
        }

        private Shared(Optional<ModelOccurrence> where, boolean reusing,
                       CompositionBudget countedTo) {
            this.where = where;
            this.reusing = reusing;
            this.mostParts = countedTo.maximum();
        }
    }

    /** What a step came to, and how each carried value it read was supposed then — absent where
     *  nothing supposed it. */
    private record Kept(Map<ACarriedValue, Optional<Boolean>> read, Proposition concluded) {}

    private final Shared shared;
    private final Map<ACarriedValue, Boolean> supposed;

    /** A concluding of a condition at {@code where}, where the reader knows it. */
    public Conclusion(Optional<ModelOccurrence> where) {
        this(new Shared(where, false), Map.of());
    }

    private Conclusion(Shared shared, Map<ACarriedValue, Boolean> supposed) {
        this.shared = shared;
        this.supposed = supposed;
    }

    /**
     * A concluding that concludes each step once, however many derivations it is asked of hold it.
     *
     * <p>For asking what the candidates for one expression state while a reading tries them, where
     * each candidate holds the steps of the parts under it and those were concluded when the parts
     * were read: a derivation is a value, so what a step concludes under one supposition does not
     * change. The parts left unread are numbered here as they are first met and not again, which
     * is no numbering of a condition — what such a concluding is good for is what is stated, and
     * not which number a part nothing read is given.
     */
    public static Conclusion reusing() {
        return new Conclusion(new Shared(Optional.empty(), true), Map.of());
    }

    /** This concluding, with what {@code carried} stands for supposed to have come out as
     *  {@code holds}. */
    public Conclusion supposing(ACarriedValue carried, boolean holds) {
        Map<ACarriedValue, Boolean> more = new HashMap<>(supposed);
        more.put(Objects.requireNonNull(carried, "a supposition is of some carried value"), holds);
        return new Conclusion(shared, Map.copyOf(more));
    }

    /** What {@code step} concludes. */
    public Proposition of(Derivation step) {
        if (shared.reusing) {
            for (Kept each : shared.kept.getOrDefault(step, List.of())) {
                if (agrees(each.read())) {
                    readAll(each.read().keySet());
                    return each.concluded();
                }
            }
        }
        shared.reading.push(new HashSet<>());
        Proposition out;
        Set<ACarriedValue> read;
        try {
            out = step.conclusion(this);
        } finally {
            read = shared.reading.pop();
        }
        // Counted as each step is concluded, so the steps it is made of are each within the figure
        // already and what is kept of it — here and by whoever asks again — is the step given up.
        if (partsIn(out) > PARTS.maximum()) {
            out = unread(new Derivation.Stopped(new WhyUnread.MorePartsThanAreConcluded(), false));
        }
        if (shared.reusing) {
            Map<ACarriedValue, Optional<Boolean>> how = new HashMap<>();
            read.forEach(each -> how.put(each, Optional.ofNullable(supposed.get(each))));
            shared.kept.computeIfAbsent(step, _ -> new ArrayList<>())
                    .add(new Kept(Map.copyOf(how), out));
        }
        readAll(read);
        shared.last.put(step, out);
        return out;
    }

    /**
     * A counting of parts written out, counted as a step is ({@link #partsIn}) and no further than
     * one past {@code figure} — for one that counts many statements sharing parts, each part
     * counted once and then known.
     */
    static Conclusion countingTo(CompositionBudget figure) {
        return new Conclusion(new Shared(Optional.empty(), false, figure), Map.of());
    }

    /** How many parts {@code stated} comes to written out, as {@link #countingTo} counts. */
    long partsWrittenOut(Proposition stated) {
        return partsIn(stated);
    }

    /**
     * How many parts {@code stated} comes to written out — each part as many times as it is held,
     * the statements a count is taken over among them — or one past the figure, where it is past
     * it.
     */
    private long partsIn(Proposition stated) {
        Long known = shared.parts.get(stated);
        if (known != null) {
            return known;
        }
        // Its parts, and the statements a count or a sum in it is taken over, which a reader of the
        // number walks as much as a part.
        long out = 1 + partsIn(stated.partsHeld()) + switch (stated) {
            case Proposition.Compared compared -> switch (compared.relation()) {
                case Relation.Affine affine -> {
                    long held = 0;
                    for (Quantity each : affine.form().coefs().keySet()) {
                        held += partsIn(each);
                    }
                    yield held;
                }
                case Relation.Ordered _ -> 0;
            };
            case Proposition.All _, Proposition.Any _, Proposition.OnAnApplication _,
                 Proposition.Some _, Proposition.SomeReachable _, Proposition.Always _,
                 Proposition.Truth _, Proposition.InCases _, Proposition.Present _,
                 Proposition.SameValue _, Proposition.LastToHold _, Proposition.Unread _,
                 Proposition.Carried _, Proposition.SoManyHold _,
                 Proposition.WhereItAnswers _ -> 0;
        };
        long kept = Math.min(out, shared.mostParts + 1L);
        shared.parts.put(stated, kept);
        return kept;
    }

    private long partsIn(List<Proposition> each) {
        long out = 0;
        for (Proposition one : each) {
            out += partsIn(one);
        }
        return out;
    }

    /** The parts the statements {@code quantity} is a count or a sum over come to. */
    private long partsIn(Quantity quantity) {
        return switch (quantity) {
            case Quantity.HowManyMeet(DecisionSubject _, Proposition each) -> partsIn(each);
            case Quantity.HowManyHold(List<Proposition> each) -> partsIn(each);
            case Quantity.SumOver(DecisionSubject _, Quantity each) -> partsIn(each);
            case Quantity.WhatAnOperationAnswers answers -> {
                long out = 0;
                for (Quantity each : answers.of()) {
                    out += partsIn(each);
                }
                yield out;
            }
            case Quantity.APieceOf piece -> partsIn(piece.string());
            case Quantity.IsAmongThePieces among ->
                    partsIn(among.value()) + partsIn(among.string());
            case DecisionAtom.OfTheInput _, DecisionAtom.OfAnAnswer _,
                 DecisionAtom.TakenOfAnAnswer _, DecisionAtom.ComputedOverAnAnswer _,
                 Quantity.OfABinding _,
                 Quantity.CodePointsOfAPiece _, Quantity.HowManyDifferent _,
                 Quantity.RemainderOfADividend _, Quantity.RemainderByAnInput _,
                 Quantity.ProductOfTwo _, Quantity.HowManyCarried _ -> 0;
        };
    }

    /** What {@code how} concludes, beside {@code how}: the one way a meaning is made. */
    public MeaningsOfABody.Meaning meaningOf(Derivation how) {
        return new MeaningsOfABody.Meaning(of(how), how);
    }

    /** What {@code step} concluded the last time it was concluded here, or null where it was not. */
    public Proposition concludedAt(Derivation step) {
        return shared.last.get(step);
    }

    /**
     * Some element of {@code container} meeting {@code element} — or, where {@code element}
     * quantifies {@code container} already, a part nothing read: two elements of one container
     * said of one element would be one subject ({@link Proposition.Some}). Every quantifier a
     * derivation concludes is made here, so no reading of two elements reaches a reader as one.
     */
    Proposition someElement(DecisionSubject container, Proposition element) {
        return Proposition.Some.quantifiesOver(container, element)
                ? twoElementsAsOne()
                : new Proposition.Some(container, element, true);
    }

    /**
     * Some element of {@code container} meeting {@code element}, where {@code element} picks out
     * the one element worked out — the entry a lookup found — and so where that one answers is
     * where the whole does: its divisor nought stops the run, and no other element is asked.
     * Read as some element meeting it where it holds, on the rows no element it picks out answers
     * nothing on ({@link #someElement}, of statements every row answers).
     */
    Proposition theEntryMeeting(DecisionSubject container, Proposition element) {
        Proposition answers = Proposition.whereItAnswersAtAll(element);
        return answers == null ? someElement(container, element)
                : Proposition.whereItAnswers(someElement(container, answers.denied()).denied(),
                        someElement(container, Proposition.whereItHolds(element)));
    }

    /**
     * {@code element} said of one element of {@code container} that a lookup picked out — or,
     * where {@code element} quantifies {@code container}, a part nothing read. The element picked
     * out stands at {@code container[*]} with no quantifier around it, so a quantifier over
     * {@code container} inside {@code element} takes it for its own element, and the two are one
     * subject just as two quantifiers would make them.
     */
    Proposition ofOneElement(DecisionSubject container, Proposition element) {
        return Proposition.Some.quantifiesOver(container, element) ? twoElementsAsOne() : element;
    }

    private Proposition twoElementsAsOne() {
        return unread(new Derivation.Stopped(new WhyUnread.TwoElementsOfOneContainer(), false));
    }

    /**
     * A part nothing read, for a statement about elements where what is stated of one may answer
     * nothing on some rows and nothing says which element a run reaches first
     * ({@link HowTheElementsAreAsked}): a quantifier, a count or a search is of statements every row
     * answers, so the one a step would make is not made.
     */
    Proposition whichElementARunStopsAt() {
        return unread(new Derivation.Stopped(new WhyUnread.WhichElementARunStopsAt(), false));
    }

    Proposition unread(Derivation.Stopped stopped) {
        return new Proposition.Unread(shared.where, shared.unread++, stopped.why(),
                stopped.fixed(), true);
    }

    /** What {@code carried} is supposed to have come out as, or itself where nothing supposes it. */
    Proposition carried(ACarriedValue carried) {
        readAll(Set.of(carried));
        Boolean holds = supposed.get(carried);
        return holds != null ? new Proposition.Always(holds) : new Proposition.Carried(carried, true);
    }

    /** Whether each carried value {@code read} says how it was supposed is supposed so here. */
    private boolean agrees(Map<ACarriedValue, Optional<Boolean>> read) {
        for (Map.Entry<ACarriedValue, Optional<Boolean>> each : read.entrySet()) {
            if (!each.getValue().equals(Optional.ofNullable(supposed.get(each.getKey())))) {
                return false;
            }
        }
        return true;
    }

    /** That the step being concluded read {@code carried}. */
    private void readAll(Set<ACarriedValue> carried) {
        Set<ACarriedValue> into = shared.reading.peek();
        if (into != null) {
            into.addAll(carried);
        }
    }
}
