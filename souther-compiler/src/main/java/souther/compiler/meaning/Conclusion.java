package souther.compiler.meaning;

import souther.compiler.numeric.UnheldNumber;
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

    /**
     * How many ways of keeping elements a statement over them is written out from
     * ({@link CompositionBudget#WAYS_A_STATEMENT_IS_WRITTEN_OUT_OVER}), read here and nowhere
     * else.
     */
    private static final CompositionBudget WAYS =
            CompositionBudget.WAYS_A_STATEMENT_IS_WRITTEN_OUT_OVER;

    /**
     * The most ways that are written out where a statement over them is concluded. A statement
     * over more is held as what its cases are written out from, and written out where a reader
     * asks for them.
     */
    private static final long WRITTEN_AT_ONCE = 64;

    /** Whether the cases of a statement over {@code kept} are written out where it is concluded. */
    static boolean writtenAtOnce(KeptWays kept) {
        return kept.work(kept.undecided(), WRITTEN_AT_ONCE + 1, false) <= WRITTEN_AT_ONCE;
    }

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
        /** Where the numbers a statement over the ways is owed start, by what it is written out
         *  from, so that the statement met again here is owed the same ones. */
        private final Map<Spelling, Long> reserved = new HashMap<>();
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
        out = withinTheParts(out);
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
     * {@code out}, or the step given up where it comes to more parts than a step is concluded
     * with.
     *
     * <p>Counted as each step is concluded, so the steps it is made of are each within the figure
     * already and what is kept of it — here and by whoever asks again — is the step given up.
     */
    private Proposition withinTheParts(Proposition out) {
        return pastTheParts(out)
                ? unread(new Derivation.Stopped(new WhyUnread.MorePartsThanAreConcluded(), false))
                : out;
    }

    /** Whether {@code stated} comes to more parts than a step is concluded with. */
    private boolean pastTheParts(Proposition stated) {
        return partsIn(stated) > PARTS.maximum();
    }

    /**
     * What a comparison over the ways its elements are kept states: every way written out where
     * there are few, and otherwise held as what its cases are written out from
     * ({@link Proposition.OfTheWays}), with the conditions and the reading concluded now.
     *
     * <p>How many ways there are is what writing them out costs, and not how many parts they come
     * to, which the ways written out say: alike, they come to a few. So it is the work that is
     * bounded here, and what the cases come to is counted as they are written out. Past the
     * figure they are not written out, and the statement is a part nothing read.
     */
    Proposition overTheWays(Derivation.WaysWrittenWhenAsked ways) {
        KeptWays kept = ways.kept();
        long cases = kept.work(kept.undecided(), WAYS.maximum() + 1, false);
        if (cases > WAYS.maximum()) {
            return unread(new Derivation.Stopped(new WhyUnread.MoreWaysThanAreWrittenOut(),
                    ways.fixed()));
        }
        if (writtenAtOnce(kept)) {
            return of(ways.ways());
        }
        Map<Integer, Proposition> conditions = new HashMap<>();
        ways.conditions().forEach((truth, condition) -> conditions.put(truth, of(condition)));
        Proposition reading = of(ways.reading());
        long owed = numbersOwed(cases);
        Spelling spelled = new Proposition.WaysToWrite(kept, conditions, reading, ways.forms(),
                ways.sum(), ways.count(), ways.counted(), ways.fixed(), shared.where, 0, owed)
                .spelled();
        Long first = shared.reserved.get(spelled);
        if (first == null) {
            first = (long) shared.unread;
            shared.unread += (int) owed;
            shared.reserved.put(spelled, first);
        }
        return new Proposition.OfTheWays(new Proposition.WaysToWrite(kept, conditions, reading,
                ways.forms(), ways.sum(), ways.count(), ways.counted(), ways.fixed(), shared.where,
                first, owed), true);
    }

    /**
     * How many numbers the cases of {@code cases} ways are written out with at the most. A part
     * nothing read is made at a way, where a number of it cannot be held, or at a step that joins
     * two ways, where it comes to more parts than a step is concluded with; never twice at one.
     * The steps are a tree whose every step joins two, so there is one fewer of them than there
     * are ways.
     */
    private static long numbersOwed(long cases) {
        return 2 * cases - 1;
    }

    /**
     * The cases of a statement over the ways, written out from what it is held as: every way,
     * decided in turn, with the totals it makes given to the reading.
     *
     * <p>Each part nothing read the cases come to is numbered from where the statement was
     * concluded to be owed them, so the cases are the same however often and by whoever they are
     * written out, and none of them is numbered as a part that is concluded beside the statement.
     * Counted as each step of them is, as a step of a derivation is concluded.
     */
    static Proposition writtenOutOver(Proposition.WaysToWrite ways) {
        Conclusion at = new Conclusion(new Shared(ways.where(), false), Map.of());
        at.shared.unread = (int) ways.firstNumber();
        KeptWays kept = ways.kept();
        Proposition written = writtenOutBy(at, ways, kept);
        if (at.shared.unread > ways.firstNumber() + ways.numbersOwed()) {
            throw new IllegalStateException("the cases of ways were written out with more numbers"
                    + " than they were owed: " + (at.shared.unread - ways.firstNumber()) + " of "
                    + ways.numbersOwed());
        }
        return written;
    }

    /**
     * The cases, or the one part nothing read they are given up as where a step of them past the
     * figure is needed to say what they come to.
     *
     * <p>A step past the figure stands as a part nothing read while it is joined on, so that a
     * step above it that does not need it — one whose condition decides against it — is joined as
     * it would have been. The cases are one step, though, and a part nothing read that stands
     * for each step past the figure that is still needed would be told of once for each: the
     * step above a given-up one is small again, so the cases would hold as many of them as there
     * are such steps. Where one is still there when the cases are joined, the cases are given up
     * as that one part.
     */
    private static Proposition writtenOutBy(Conclusion at, Proposition.WaysToWrite ways,
                                            KeptWays kept) {
        Set<Integer> givenUp = new HashSet<>();
        Proposition[] first = new Proposition[1];
        Proposition written = kept.made(new KeptWays.Making<Proposition>() {
            @Override
            public Proposition split(int truth, Proposition where, Proposition otherwise) {
                Proposition joined = Derivation.IfThenElse.joined(
                        ways.conditions().get(truth), where, otherwise);
                if (!at.pastTheParts(joined)) {
                    return joined;
                }
                Proposition.Unread past = (Proposition.Unread) at.unread(new Derivation.Stopped(
                        new WhyUnread.MorePartsThanAreConcluded(), false));
                givenUp.add(past.ordinal());
                if (first[0] == null) {
                    first[0] = past;
                }
                return past;
            }

            @Override
            public Proposition leaf(Boolean[] decided) {
                return Derivation.WithTheTotalsOfAWay.stated(at, ways.reading(),
                        ways.sum(), kept.thereOf(ways.forms(), decided), ways.count(),
                        kept.countThere(ways.forms().size(), ways.counted(), decided),
                        ways.fixed());
            }
        }, kept.undecided());
        return givenUp.isEmpty() || !stands(written, givenUp) ? written : first[0];
    }

    /** Whether a part nothing read numbered as one of {@code numbers} stands in {@code stated}. */
    private static boolean stands(Proposition stated, Set<Integer> numbers) {
        return stated instanceof Proposition.Unread unread
                ? numbers.contains(unread.ordinal())
                : stated.partsHeld().stream().anyMatch(part -> stands(part, numbers));
    }

    /** A part nothing read, for a number of a way that cannot be held. */
    Proposition numberNotHeld(UnheldNumber why, boolean fixed) {
        return unread(new Derivation.Stopped(new WhyUnread.ANumberNotHeld(why), fixed));
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
        // A statement held as how it is written out is one part until it is written out, and is
        // counted against the figure then, as the step that writes it out concludes it.
        if (stated instanceof Proposition.OfTheWays) {
            shared.parts.put(stated, 1L);
            return 1;
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
            case Proposition.StringInside inside ->
                    partsIn(inside.inner()) + partsIn(inside.outer());
            case Proposition.All _, Proposition.Any _, Proposition.OnAnApplication _,
                 Proposition.Some _, Proposition.SomeReachable _, Proposition.Always _,
                 Proposition.Truth _, Proposition.InCases _, Proposition.Present _,
                 Proposition.InTheStrings _, Proposition.SameValue _,
                 Proposition.LastToHold _, Proposition.Unread _,
                 Proposition.Carried _, Proposition.SoManyHold _,
                 Proposition.WhereItAnswers _, Proposition.OfTheWays _ -> 0;
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
            case Quantity.HowManyDifferentMeet different ->
                    partsIn(different.meeting().statement());
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
            case Quantity.ThePieceAt piece -> partsIn(piece.string());
            case Quantity.IsAmongThePieces among ->
                    partsIn(among.value()) + partsIn(among.string());
            case DecisionAtom.OfTheInput _, DecisionAtom.OfAnAnswer _,
                 DecisionAtom.TakenOfAnAnswer _, DecisionAtom.ComputedOverAnAnswer _,
                 Quantity.OfABinding _, Quantity.TheKeptTotal _,
                 Quantity.CodePointsOfAPiece _, Quantity.HowManyDifferent _,
                 Quantity.HowManyDifferentBelow _, Quantity.HowManyDifferentAcross _,
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
