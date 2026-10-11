package souther.compiler.meaning;

import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.types.ModelOccurrence;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.SortedMap;
import java.util.TreeMap;

/**
 * What a condition states, about the subjects it is finally about.
 *
 * <p>Told apart by what it states and by nothing else: {@code p && q} and {@code q && p} are one
 * proposition, so are {@code p || p} and {@code p}, and so are every spelling of one comparison. A
 * conjunction or a disjunction is made through {@link #all} and {@link #any}, which put their parts in
 * one order and keep each once. Which construct each part was read from, and in what order a run
 * meets them, are not here: the first is {@link WhatAConditionSays}'s and the second the run's.
 *
 * <p>Denial is pushed down to the parts ({@link #denied}), so there is no arm for it: what a part
 * holds or fails is the {@code holds} it carries, and a quantifier denied is the other quantifier.
 */
public sealed interface Proposition {

    /** What holds exactly where this does not. */
    Proposition denied();

    /**
     * A spelling that tells two propositions apart exactly where they are two, and orders parts.
     *
     * <p>Spelled once, when the proposition is made: it is what parts are kept once and put in order
     * by, and asked of every part each time parts are joined, so a spelling built on asking would be
     * built again for every join a part goes into.
     */
    String key();

    /**
     * Whether this can come out one way for one element of the container at {@code container} and
     * the other way for another: whether it names a subject an element is, or holds something
     * nothing here sees into.
     *
     * <p>What cannot is the same for every element, so some element meeting it is it and the
     * container holding something — and a quantifier left holding it would turn on the container
     * without any part of it saying so.
     */
    default boolean mayTurnOnAnElementOf(DecisionSubject container) {
        return switch (this) {
            case Always _, Carried _ -> false;
            case Unread unread -> !unread.fixed();
            case Compared compared -> switch (compared.relation()) {
                case Relation.Affine affine -> affine.form().coefs().keySet().stream()
                        .anyMatch(quantity -> mayBeAnElementOf(quantity, container));
                case Relation.Ordered ordered -> mayBeAnElementOf(ordered.term(), container);
            };
            case Truth truth -> mayBeAnElementOf(truth.of(), container);
            case InCases cases -> mayBeAnElementOf(cases.of(), container);
            case Present present -> mayBeAnElementOf(present.of(), container);
            case SameValue same -> mayBeAnElementOf(same.one(), container)
                    || mayBeAnElementOf(same.other(), container);
            case LastToHold last ->
                    isAnElementOf(new DecisionSubject.AnInput(last.position()), container);
            case All all -> all.parts().stream()
                    .anyMatch(part -> part.mayTurnOnAnElementOf(container));
            case Any any -> any.parts().stream()
                    .anyMatch(part -> part.mayTurnOnAnElementOf(container));
            case OnAnApplication applications -> applications.each().stream()
                    .anyMatch(one -> one.mayTurnOnAnElementOf(container));
            case Some some -> isAnElementOf(some.container(), container)
                    || some.ofTheElement().mayTurnOnAnElementOf(container);
            // What it is written over is not what it is about, so it is taken to turn on an element
            // wherever it might, as a part nothing sees into is.
            case SomeReachable reached ->
                    isAnElementOf(new DecisionSubject.AnInput(reached.at()), container)
                            || reached.atANode().mayTurnOnAnElementOf(container);
        };
    }

    /** Whether {@code quantity} may be read off an element of {@code container}. A value a body
     *  bound or a dependency answered is computed from something nothing here names, so it may. */
    private static boolean mayBeAnElementOf(Quantity quantity, DecisionSubject container) {
        return switch (quantity) {
            case DecisionAtom.OfTheInput(var term) ->
                    isAnElementOf(new DecisionSubject.AnInput(term.subjectPath()), container);
            case DecisionAtom.OfAnAnswer _, Quantity.OfABinding _ -> true;
            case DecisionAtom.TakenOfAnAnswer(var _, var _, var taken, var _) ->
                    isAnElementOf(taken, container);
            // A piece of a string is whatever the statement it is read inside says it is, and
            // that statement is about the string and no container's element.
            case Quantity.CodePointsOfAPiece _ -> false;
            case Quantity.HowManyMeet(DecisionSubject counted, Proposition each) ->
                    isAnElementOf(counted, container) || each.mayTurnOnAnElementOf(container);
            case Quantity.HowManyHold(List<Proposition> each) -> each.stream()
                    .anyMatch(one -> one.mayTurnOnAnElementOf(container));
            case Quantity.HowManyDifferent(DecisionSubject counted, DecisionSubject _) ->
                    isAnElementOf(counted, container);
            case Quantity.SumOver(DecisionSubject summed, var each) ->
                    isAnElementOf(summed, container) || each.coefs().keySet().stream()
                            .anyMatch(one -> mayBeAnElementOf(one, container));
            case Quantity.RemainderOfADividend(var dividend, var _) -> dividend.coefs().keySet()
                    .stream().anyMatch(term -> isAnElementOf(
                            new DecisionSubject.AnInput(term.subjectPath()), container));
        };
    }

    /** Whether {@code subject} may be an element of {@code container}, the same way. */
    private static boolean mayBeAnElementOf(DecisionSubject subject, DecisionSubject container) {
        return switch (subject) {
            case DecisionSubject.AnInput _ -> isAnElementOf(subject, container);
            case DecisionSubject.AnAnswer _ -> true;
        };
    }

    /** Whether {@code at} is an element of {@code container}, or a key of it, or under one. */
    private static boolean isAnElementOf(DecisionSubject at, DecisionSubject container) {
        return at.isAtOrUnder(container.element()) || at.isAtOrUnder(container.key());
    }

    /** Comes out {@code holds} for every row. */
    record Always(boolean holds) implements Proposition {

        @Override
        public Proposition denied() {
            return new Always(!holds);
        }

        @Override
        public String key() {
            return String.valueOf(holds);
        }
    }

    /**
     * A relation over quantities, held or failing.
     *
     * @param key spelled from the rest when it is made, whatever is handed in
     */
    record Compared(Relation relation, boolean holds, String key) implements Proposition {

        public Compared(Relation relation, boolean holds) {
            this(relation, holds, null);
        }

        public Compared {
            if (relation == null) {
                throw new IllegalArgumentException("a comparison states some relation");
            }
            if (ofACount(relation) != null) {
                throw new IllegalArgumentException("a count held against nought is whether some"
                        + " element meets what is counted, and is written as that: " + relation);
            }
            key = (holds ? "" : "!") + relation;
        }

        @Override
        public Proposition denied() {
            return new Compared(relation, !holds);
        }
    }

    /**
     * A subject read for its truth, holding or failing.
     *
     * @param key spelled from the rest when it is made, whatever is handed in
     */
    record Truth(DecisionSubject of, boolean holds, String key) implements Proposition {

        public Truth(DecisionSubject of, boolean holds) {
            this(of, holds, null);
        }

        public Truth {
            if (of == null) {
                throw new IllegalArgumentException("a truth is a truth of something");
            }
            key = (holds ? "" : "!") + of.spelled();
        }

        @Override
        public Proposition denied() {
            return new Truth(of, !holds);
        }
    }

    /**
     * A subject being one of {@code cases}, or not.
     *
     * <p>The cases selected and not the fork that selected them: a match of three arms is three
     * propositions about one subject, one per arm.
     *
     * @param key spelled from the rest when it is made, whatever is handed in
     */
    record InCases(DecisionSubject of, CasesLeft cases, boolean holds, String key)
            implements Proposition {

        public InCases(DecisionSubject of, CasesLeft cases, boolean holds) {
            this(of, cases, holds, null);
        }

        public InCases {
            if (of == null || cases == null) {
                throw new IllegalArgumentException("a case is some subject's, and some cases");
            }
            key = (holds ? "" : "!") + of.spelled() + " is " + cases.spelled();
        }

        @Override
        public Proposition denied() {
            return new InCases(of, cases, !holds);
        }
    }

    /**
     * An optional subject holding a value, or not.
     *
     * @param key spelled from the rest when it is made, whatever is handed in
     */
    record Present(DecisionSubject of, boolean holds, String key) implements Proposition {

        public Present(DecisionSubject of, boolean holds) {
            this(of, holds, null);
        }

        public Present {
            if (of == null) {
                throw new IllegalArgumentException("a value is present at some subject");
            }
            key = (holds ? "" : "!") + "present " + of.spelled();
        }

        @Override
        public Proposition denied() {
            return new Present(of, !holds);
        }
    }

    /**
     * Two subjects holding the same value, or not — what a container holding a value asks of one
     * of its elements.
     *
     * @param key spelled from the rest when it is made, whatever is handed in
     */
    record SameValue(DecisionSubject one, DecisionSubject other, boolean holds, String key)
            implements Proposition {

        public SameValue(DecisionSubject one, DecisionSubject other, boolean holds) {
            this(one, other, holds, null);
        }

        public SameValue {
            if (one == null || other == null) {
                throw new IllegalArgumentException("a sameness is of two subjects");
            }
            key = one.spelled() + (holds ? " == " : " /= ") + other.spelled();
        }

        @Override
        public Proposition denied() {
            return new SameValue(one, other, !holds);
        }
    }

    /**
     * The element of the container at {@code container} that a statement is about is the last of
     * those holding, at {@code position}, the value it holds there — or, where not {@code holds},
     * one that a later element holds the same value as.
     *
     * <p>Said of the element a quantifier over the container is about, so it is a part of what is
     * asked of that element and names no other. It is what a map filed from a list adds to the
     * element it answers: the entry under a key is the last element of that key, and an earlier
     * one is in no entry.
     *
     * @param position a position under the container's element, which an element is told apart
     *                 from the others by
     * @param key      spelled from the rest when it is made, whatever is handed in
     */
    record LastToHold(TermPath container, TermPath position, boolean holds, String key)
            implements Proposition {

        public LastToHold(TermPath container, TermPath position, boolean holds) {
            this(container, position, holds, null);
        }

        public LastToHold {
            if (container == null || position == null) {
                throw new IllegalArgumentException("a last is of a container's element by a place");
            }
            key = (holds ? "last " : "not last ") + container + " by " + position;
        }

        @Override
        public Proposition denied() {
            return new LastToHold(container, position, !holds);
        }
    }

    /**
     * Every part holding. Made through {@link #all}.
     *
     * @param key spelled from the parts' own when it is made, whatever is handed in
     */
    record All(List<Proposition> parts, String key) implements Proposition {

        public All(List<Proposition> parts) {
            this(parts, null);
        }

        public All {
            parts = List.copyOf(parts);
            if (parts.size() < 2) {
                throw new IllegalArgumentException("a conjunction is of two or more parts");
            }
            key = "all" + parts.stream().map(Proposition::key).toList();
        }

        @Override
        public Proposition denied() {
            return any(parts.stream().map(Proposition::denied).toList());
        }
    }

    /**
     * Some part holding. Made through {@link #any}.
     *
     * @param key spelled from the parts' own when it is made, whatever is handed in
     */
    record Any(List<Proposition> parts, String key) implements Proposition {

        public Any(List<Proposition> parts) {
            this(parts, null);
        }

        public Any {
            parts = List.copyOf(parts);
            if (parts.size() < 2) {
                throw new IllegalArgumentException("a disjunction is of two or more parts");
            }
            key = "any" + parts.stream().map(Proposition::key).toList();
        }

        @Override
        public Proposition denied() {
            return all(parts.stream().map(Proposition::denied).toList());
        }
    }

    /**
     * Some element of the container at {@code container} meeting {@code ofTheElement} — or, where
     * {@code holds} is false, no element meeting it.
     *
     * <p>The element is what stands at {@code container}'s element inside {@code ofTheElement}: a
     * subject under {@code container[*]} there is the element's — and of a map, whose element is an
     * entry, so is one under {@code container[key]} — and nothing else is. Which is why
     * the same container is never quantified twice inside one proposition: the two elements would be
     * one subject, and the proposition would say {@code x < x} where it was asked about two of them.
     *
     * @param key spelled from the rest when it is made, whatever is handed in
     */
    record Some(DecisionSubject container, Proposition ofTheElement, boolean holds, String key)
            implements Proposition {

        public Some(DecisionSubject container, Proposition ofTheElement, boolean holds) {
            this(container, ofTheElement, holds, null);
        }

        public Some {
            if (container == null || ofTheElement == null) {
                throw new IllegalArgumentException("a quantifier is over some container");
            }
            key = (holds ? "some " : "no ") + container + " [" + ofTheElement.key() + "]";
        }

        @Override
        public Proposition denied() {
            return new Some(container, ofTheElement, !holds);
        }
    }

    /**
     * What a walk carried into the step being read coming out on the side its end is asked about —
     * or, where {@code holds} is false, not.
     *
     * <p>Made only while a walk's step is concluded with nothing supposing what it carried, which a
     * reading does to decide how the walk closes: the same for every element the walk is handed,
     * and either way as far as anything here knows. Every concluding of a whole condition supposes
     * it ({@link Derivation.Supposing}), so no reader of what a condition states is handed one.
     *
     * @param key spelled from the rest when it is made, whatever is handed in
     */
    record Carried(ACarriedValue value, boolean holds, String key) implements Proposition {

        public Carried(ACarriedValue value, boolean holds) {
            this(value, holds, null);
        }

        public Carried {
            if (value == null) {
                throw new IllegalArgumentException("a walk carried something");
            }
            key = (holds ? "" : "!") + value;
        }

        @Override
        public Proposition denied() {
            return new Carried(value, !holds);
        }

        /** What a reader of what a condition states throws, handed one: a walk's step concluded
         *  outside every supposition of what it carried. */
        public IllegalStateException handedToAReader() {
            return new IllegalStateException(value + " is supposed wherever a condition is"
                    + " concluded whole, and reached a reader of it unsupposed");
        }
    }

    /**
     * Some node reachable from the one at {@code at} meeting {@code atANode} — the node itself, or
     * one an element of a container under {@code through} on a node reached — or, where
     * {@code holds} is false, none doing so.
     *
     * <p>{@code atANode} is written of the node at {@code writtenAt}, and it binds that place: a
     * subject under {@code writtenAt} there is the same place under the node reached, and every
     * other subject is the one it names wherever the node is. So the subjects it is written over do
     * not say what it is about, and nothing reads them as a statement of the input: a reader of what
     * holds where takes {@link #surely}, which says it of the subjects as they stand.
     *
     * <p>How deep a run goes is not bounded here. A reader that sees only so far into the input has
     * {@link #surely} for each side, which holds of a row only where the search comes out that way
     * whatever lies further down, and holding of neither says nothing of which way it comes out.
     *
     * @param through   the fields of a node whose elements are the nodes below it, in one order
     * @param noneBelow that the node at {@code at} has no node below it, where {@code at} is
     *                  {@code writtenAt} and the containers under it are measured
     * @param key       spelled from the rest when it is made, whatever is handed in
     */
    record SomeReachable(TermPath at, TermPath writtenAt, List<String> through,
                         Proposition atANode, Optional<Proposition> noneBelow, boolean holds,
                         String key) implements Proposition {

        public SomeReachable(TermPath at, TermPath writtenAt, List<String> through,
                             Proposition atANode, Optional<Proposition> noneBelow, boolean holds) {
            this(at, writtenAt, through, atANode, noneBelow, holds, null);
        }

        public SomeReachable {
            if (at == null || writtenAt == null || atANode == null || noneBelow == null) {
                throw new IllegalArgumentException("a search is from a node, of something on one");
            }
            through = List.copyOf(through);
            if (through.isEmpty()) {
                throw new IllegalArgumentException("a search goes below a node through something");
            }
            key = (holds ? "reachable " : "unreachable ") + at + " from " + writtenAt + " through "
                    + through + " [" + atANode.key() + "]";
        }

        @Override
        public Proposition denied() {
            return new SomeReachable(at, writtenAt, through, atANode, noneBelow, !holds);
        }

        /**
         * What holds of a row only where this comes out as {@code outcome} whatever lies below the
         * node — the node meeting the statement for a search that some node does, the node meeting
         * it not and having nothing below for one that none does — and never holds where that is not
         * said of the subjects as they stand.
         */
        public Proposition surely(boolean outcome) {
            if (!at.equals(writtenAt)) {
                return new Always(false);
            }
            // The outcome asked is the one some node meeting the statement gives.
            if (outcome == holds) {
                return atANode;
            }
            return noneBelow.<Proposition>map(none -> all(List.of(atANode.denied(), none)))
                    .orElse(new Always(false));
        }
    }

    /**
     * Part of a condition nothing read the meaning of, told apart by where the reading stopped.
     *
     * <p>The one proposition told apart by a name. Two parts nothing could read mean nothing to be
     * told apart by, so without one they would be one part, and a condition stating two things
     * nobody read would read as stating one.
     *
     * @param where   the construct of the model the condition is, where the reader knows it — a
     *                reader asking only which answers a condition can give has no construct to name
     *                and needs none, since it never compares two unread parts
     * @param ordinal which unread part of the condition this is, in the order the reading met them
     * @param why     what stopped it, in the stopping reader's words
     * @param fixed   whether it is the same whatever the input, which is all that is known of it
     * @param key     spelled from where and which it is when it is made, whatever is handed in
     */
    record Unread(Optional<ModelOccurrence> where, int ordinal, WhyUnread why, boolean fixed,
                  boolean holds, String key) implements Proposition {

        public Unread(Optional<ModelOccurrence> where, int ordinal, WhyUnread why, boolean fixed,
                      boolean holds) {
            this(where, ordinal, why, fixed, holds, null);
        }

        public Unread {
            if (where == null || why == null) {
                throw new IllegalArgumentException("an unread part stopped somewhere, for a reason");
            }
            key = (holds ? "" : "!") + "unread " + where.map(String::valueOf).orElse("")
                    + "#" + ordinal;
        }

        @Override
        public Proposition denied() {
            return new Unread(where, ordinal, why, fixed, !holds);
        }
    }

    /**
     * What a condition inside a closure states on one application of it, where each application
     * hands the closure one of the values a container was written with: {@code each} is what it
     * states on each of them. Made through {@link #onAnApplication}.
     *
     * <p>Neither a disjunction nor a conjunction of them. A run meets the condition on an
     * application, and what holds there is that application's statement — and where the condition
     * fails, that statement's denial, on the same application. So it is denied statement by
     * statement, and whether it can hold is whether some statement can, as whether it can fail is
     * whether some denial can.
     *
     * <p><b>The applications a closure may be handed, and not the ones a run makes.</b> An
     * operation that stops at an answer hands what comes after it nothing — {@code List.any} stops
     * at the first element that holds — so a statement here may be of an application no run
     * reaches. Read for what can hold, that is a statement too many and never one too few; read for
     * what must, it would be a claim about a run that never happens. So a reader takes this only
     * for what can come out, and one that needs what must — what a path assumes, what a row is
     * asked for — declines it.
     *
     * @param key spelled from the statements' own when it is made, whatever is handed in
     */
    record OnAnApplication(List<Proposition> each, String key) implements Proposition {

        public OnAnApplication(List<Proposition> each) {
            this(each, null);
        }

        public OnAnApplication {
            each = List.copyOf(each);
            if (each.size() < 2) {
                throw new IllegalArgumentException(
                        "a condition read on its applications states two or more things");
            }
            key = "on an application" + each.stream().map(Proposition::key).toList();
        }

        @Override
        public Proposition denied() {
            return onAnApplication(each.stream().map(Proposition::denied).toList());
        }
    }

    /**
     * What a condition states on one of the applications {@code each} is read on, each statement
     * kept once in one order, and one statement where every application states it.
     */
    static Proposition onAnApplication(List<Proposition> each) {
        SortedMap<String, Proposition> kept = new TreeMap<>();
        each.forEach(one -> kept.putIfAbsent(one.key(), one));
        if (kept.isEmpty()) {
            throw new IllegalArgumentException("a condition is read on some application");
        }
        return kept.size() == 1 ? kept.firstEntry().getValue()
                : new OnAnApplication(List.copyOf(kept.values()));
    }

    /**
     * Whether some part of {@code stated} is one nothing read. A count holds none
     * ({@link Quantity.HowManyMeet}), so a comparison is read through wherever it was made.
     */
    static boolean leavesSomethingUnread(Proposition stated) {
        return firstStopIn(stated) != null;
    }

    /** Why the first part of {@code stated} nothing read stopped, in the order its parts are
     *  kept, or null where every part was read. */
    static WhyUnread firstStopIn(Proposition stated) {
        List<WhyUnread> stops = stopsIn(stated);
        return stops.isEmpty() ? null : stops.getFirst();
    }

    /** Why each part of {@code stated} nothing read stopped, in the order its parts are kept. */
    static List<WhyUnread> stopsIn(Proposition stated) {
        List<WhyUnread> out = new ArrayList<>();
        stopsIn(stated, out);
        return List.copyOf(out);
    }

    private static void stopsIn(Proposition stated, List<WhyUnread> into) {
        switch (stated) {
            case Unread unread -> into.add(unread.why());
            case All all -> all.parts().forEach(part -> stopsIn(part, into));
            case Any any -> any.parts().forEach(part -> stopsIn(part, into));
            case OnAnApplication applications ->
                    applications.each().forEach(one -> stopsIn(one, into));
            case Some some -> stopsIn(some.ofTheElement(), into);
            case SomeReachable reached -> stopsIn(reached.atANode(), into);
            case Always _, Compared _, Truth _, InCases _, Present _, SameValue _,
                 LastToHold _, Carried _ -> { }
        }
    }

    /**
     * Whether {@code stated} says of some element that it is the last of those holding a value —
     * which a map filed from a list says of the entry under a key.
     */
    static boolean saysTheLastToHold(Proposition stated) {
        return switch (stated) {
            case LastToHold _ -> true;
            case All all -> all.parts().stream().anyMatch(Proposition::saysTheLastToHold);
            case Any any -> any.parts().stream().anyMatch(Proposition::saysTheLastToHold);
            case OnAnApplication applications ->
                    applications.each().stream().anyMatch(Proposition::saysTheLastToHold);
            case Some some -> saysTheLastToHold(some.ofTheElement());
            case SomeReachable reached -> saysTheLastToHold(reached.atANode());
            case Always _, Compared _, Truth _, InCases _, Present _, SameValue _, Unread _,
                 Carried _ -> false;
        };
    }

    /**
     * Whether some part of {@code stated} is about what a dependency answered, rather than about
     * the input alone.
     *
     * <p>A container a quantifier or a count is over is a part as much as what each element is
     * asked: an element of a list an answer holds is a place inside that answer whatever the
     * statement about it names.
     */
    static boolean aboutAnAnswer(Proposition stated) {
        return switch (stated) {
            case Always _, Unread _, LastToHold _, Carried _ -> false;
            case Compared(Relation relation, boolean _, String _) -> switch (relation) {
                case Relation.Affine affine -> affine.form().coefs().keySet().stream()
                        .anyMatch(Proposition::anAnswerIn);
                case Relation.Ordered ordered -> anAnswerIn(ordered.term());
            };
            case Truth truth -> truth.of() instanceof DecisionSubject.AnAnswer;
            case InCases cases -> cases.of() instanceof DecisionSubject.AnAnswer;
            case Present present -> present.of() instanceof DecisionSubject.AnAnswer;
            case SameValue same -> same.one() instanceof DecisionSubject.AnAnswer
                    || same.other() instanceof DecisionSubject.AnAnswer;
            case All all -> all.parts().stream().anyMatch(Proposition::aboutAnAnswer);
            case Any any -> any.parts().stream().anyMatch(Proposition::aboutAnAnswer);
            case OnAnApplication applications ->
                    applications.each().stream().anyMatch(Proposition::aboutAnAnswer);
            case Some some -> some.container() instanceof DecisionSubject.AnAnswer
                    || aboutAnAnswer(some.ofTheElement());
            case SomeReachable reached -> aboutAnAnswer(reached.atANode());
        };
    }

    /** Whether {@code quantity} is about what a dependency answered: a number of an answer, or a
     *  number over a container an answer holds or over elements asked something of one. */
    static boolean anAnswerIn(Quantity quantity) {
        return switch (quantity) {
            case DecisionAtom.OfAnAnswer _, DecisionAtom.TakenOfAnAnswer _ -> true;
            case DecisionAtom.OfTheInput _, Quantity.OfABinding _,
                 Quantity.CodePointsOfAPiece _, Quantity.RemainderOfADividend _ -> false;
            case Quantity.HowManyMeet count -> count.container() instanceof DecisionSubject.AnAnswer
                    || aboutAnAnswer(count.ofTheElement());
            case Quantity.HowManyHold held -> held.each().stream()
                    .anyMatch(Proposition::aboutAnAnswer);
            case Quantity.HowManyDifferent different ->
                    different.container() instanceof DecisionSubject.AnAnswer
                            || different.ofTheElement() instanceof DecisionSubject.AnAnswer;
            case Quantity.SumOver sum -> sum.container() instanceof DecisionSubject.AnAnswer
                    || sum.ofTheElement().coefs().keySet().stream()
                            .anyMatch(Proposition::anAnswerIn);
        };
    }

    /**
     * {@code relation} held or failing as {@code holds}, written as what it comes to where it holds
     * a count of elements against nought ({@link #ofACount}).
     */
    static Proposition compared(Relation relation, boolean holds) {
        Proposition counted = ofACount(relation);
        if (counted == null) {
            counted = whichOfThemHold(relation);
        }
        Proposition held = counted != null ? counted : new Compared(relation, true);
        return holds ? held : held.denied();
    }

    /**
     * What a relation over how many of some statements hold says: some choice of which of them hold
     * and which do not that puts the number where the relation does — or null where the relation is
     * over anything else, or a number of them the arithmetic could not hold.
     *
     * <p>A choice that has one statement holding and not holding at once is none: the same value
     * written twice meets a statement twice or not at all.
     */
    private static Proposition whichOfThemHold(Relation relation) {
        if (!(relation instanceof Relation.Affine(LinearForm<Quantity> form, Rel rel))
                || form.coefs().size() != 1
                || !(form.coefs().keySet().iterator().next()
                        instanceof Quantity.HowManyHold(List<Proposition> each))) {
            return null;
        }
        ExactRatio by = form.coefs().values().iterator().next();
        List<Proposition> ways = new ArrayList<>();
        choices:
        for (int chosen = 0; chosen < 1 << each.size(); chosen++) {
            if (!(by.times(ExactRatio.of(Integer.bitCount(chosen)))
                    .flatMap(weighed -> weighed.plus(form.constant()))
                    instanceof ExactAnswer.Held<ExactRatio>(ExactRatio at))) {
                return null;
            }
            if (!rel.holds(at.signum())) {
                continue;
            }
            Map<String, Boolean> holding = new HashMap<>();
            List<Proposition> parts = new ArrayList<>();
            for (int i = 0; i < each.size(); i++) {
                boolean holds = (chosen & 1 << i) != 0;
                Boolean before = holding.putIfAbsent(each.get(i).key(), holds);
                if (before != null && before != holds) {
                    continue choices;
                }
                parts.add(holds ? each.get(i) : each.get(i).denied());
            }
            ways.add(all(parts));
        }
        return any(ways);
    }

    /**
     * What a relation over one count of elements meeting something says, where that is whether
     * some element meets it, or the same whatever is counted — or null where it says how many.
     *
     * <p>A count is never fewer than none and comes to none exactly where no element meets what is
     * counted. So {@code count >= 1}, {@code count > 0} and {@code count /= 0} are some element
     * meeting it, {@code count == 0} and {@code count < 1} none doing so, and {@code count >= 0}
     * every row: one statement each, made one proposition whichever was written, and the same one
     * the element that witnesses a filter's answer holding something is read as. A relation that
     * says how many beyond that — exactly one, two or more — is kept as the relation.
     */
    private static Proposition ofACount(Relation relation) {
        if (!(relation instanceof Relation.Affine(LinearForm<Quantity> form, Rel rel))
                || form.coefs().size() != 1
                || !(form.coefs().keySet().iterator().next()
                        instanceof Quantity.HowManyMeet(DecisionSubject container, Proposition each))) {
            return null;
        }
        // a·count + k rel 0 with a positive, as a relation is written: count rel t.
        ExactRatio by = form.coefs().values().iterator().next();
        ExactAnswer<ExactRatio> at = form.constant().negated().dividedBy(by);
        if (!(at instanceof ExactAnswer.Held<ExactRatio>(ExactRatio t))) {
            return null;
        }
        Proposition some = new Some(container, each, true);
        int againstNought = t.signum();
        boolean atMostOne = t.compareTo(ExactRatio.ONE) <= 0;
        boolean belowOne = t.compareTo(ExactRatio.ONE) < 0;
        return switch (rel) {
            case GE -> againstNought <= 0 ? new Always(true) : atMostOne ? some : null;
            case GT -> againstNought < 0 ? new Always(true)
                    : belowOne ? some : null;
            case EQ -> againstNought < 0 || !t.isWhole() ? new Always(false)
                    : againstNought == 0 ? some.denied() : null;
            case LE, LT, NE -> throw new IllegalStateException(
                    "a relation is written under the canonical one of it and its denial");
        };
    }

    /**
     * Every one of {@code parts} holding: what holds of all of them, with a part that always holds
     * left out, one that never does settling it, and each part kept once in one order.
     */
    static Proposition all(List<Proposition> parts) {
        return joined(parts, true);
    }

    /** Some one of {@code parts} holding, the same way round. */
    static Proposition any(List<Proposition> parts) {
        return joined(parts, false);
    }

    private static Proposition joined(List<Proposition> parts, boolean every) {
        // In the order of their spellings, a part whose spelling is already kept left out.
        SortedMap<String, Proposition> kept = new TreeMap<>();
        for (Proposition part : parts) {
            List<Proposition> flat = switch (part) {
                case All all when every -> all.parts();
                case Any any when !every -> any.parts();
                default -> List.of(part);
            };
            for (Proposition one : flat) {
                if (one instanceof Always(boolean holds)) {
                    if (holds != every) {
                        return one;
                    }
                    continue;
                }
                kept.putIfAbsent(one.key(), one);
            }
        }
        return switch (kept.size()) {
            case 0 -> new Always(every);
            case 1 -> kept.firstEntry().getValue();
            default -> every ? new All(List.copyOf(kept.values()))
                    : new Any(List.copyOf(kept.values()));
        };
    }
}
