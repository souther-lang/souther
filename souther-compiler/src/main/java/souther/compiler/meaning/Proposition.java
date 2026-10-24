package souther.compiler.meaning;

import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.types.ModelOccurrence;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;
import java.util.function.UnaryOperator;
import java.util.stream.Collectors;

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
     *
     * <p>And what each of them hashes as. It is one of the values compared, so two equal
     * propositions spell it alike, and a string keeps its hash; worked out from the parts instead, a
     * hash walks the whole proposition each time one is used as a key.
     */
    String key();

    /**
     * The statements this one holds as parts of what it states, in the order it keeps them.
     *
     * <p>The one place that says which they are. A reader asking something of every part — whether
     * one was not read, how many parts there are written out, whether one is about an answer —
     * asks this for them, so a statement a kind comes to hold is one every such reader meets. Each
     * reading the parts off the components for itself, a part added to a kind was met by none of
     * them. What a count is taken over is a statement inside a number and not a part here.
     */
    default List<Proposition> partsHeld() {
        return switch (this) {
            case All all -> all.parts();
            case Any any -> any.parts();
            case OnAnApplication applications -> applications.each();
            case SoManyHold counted -> counted.statements();
            case Some some -> List.of(some.ofTheElement());
            case WhereItAnswers where -> List.of(where.answers(), where.states());
            case SomeReachable reached -> reached.noneBelow()
                    .map(none -> List.of(reached.atANode(), none))
                    .orElseGet(() -> List.of(reached.atANode()));
            case Always _, Compared _, Truth _, InCases _, Present _, SameValue _,
                 LastToHold _, Unread _, Carried _ -> List.of();
        };
    }

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
            case LastToHold last -> isAnElementOf(last.position(), container);
            case All _, Any _, OnAnApplication _, SoManyHold _, WhereItAnswers _ ->
                    somePartMayTurnOnAnElementOf(container);
            case Some some -> isAnElementOf(some.container(), container)
                    || somePartMayTurnOnAnElementOf(container);
            // What it is written over is not what it is about, so it is taken to turn on an element
            // wherever it might, as a part nothing sees into is.
            case SomeReachable reached ->
                    isAnElementOf(new DecisionSubject.AnInput(reached.at()), container)
                            || somePartMayTurnOnAnElementOf(container);
        };
    }

    private boolean somePartMayTurnOnAnElementOf(DecisionSubject container) {
        return partsHeld().stream().anyMatch(part -> part.mayTurnOnAnElementOf(container));
    }

    /** Whether {@code quantity} may be read off an element of {@code container}. A value a body
     *  bound or a dependency answered is computed from something nothing here names, so it may. */
    private static boolean mayBeAnElementOf(Quantity quantity, DecisionSubject container) {
        return switch (quantity) {
            case DecisionAtom.OfTheInput(var term) ->
                    isAnElementOf(new DecisionSubject.AnInput(term.subjectPath()), container);
            // What a recursion carries stands for any number, which may be any element's.
            case DecisionAtom.OfAnAnswer _, Quantity.OfABinding _, Quantity.HowManyCarried _ ->
                    true;
            case DecisionAtom.TakenOfAnAnswer(var _, var _, var taken, var _) ->
                    isAnElementOf(taken, container);
            case DecisionAtom.ComputedOverAnAnswer computed ->
                    isAnElementOf(computed.list(), container);
            case Quantity.WhatAnOperationAnswers answers -> answers.of().stream()
                    .anyMatch(each -> mayBeAnElementOf(each, container));
            // A piece of a string is whatever the statement it is read inside says it is, and
            // that statement is about the string and no container's element.
            case Quantity.CodePointsOfAPiece _ -> false;
            case Quantity.APieceOf piece -> mayBeAnElementOf(piece.string(), container);
            case Quantity.IsAmongThePieces among -> mayBeAnElementOf(among.value(), container)
                    || mayBeAnElementOf(among.string(), container);
            case Quantity.HowManyMeet(DecisionSubject counted, Proposition each) ->
                    isAnElementOf(counted, container) || each.mayTurnOnAnElementOf(container);
            case Quantity.HowManyHold(List<Proposition> each) -> each.stream()
                    .anyMatch(one -> one.mayTurnOnAnElementOf(container));
            case Quantity.HowManyDifferent(DecisionSubject counted, DecisionSubject _) ->
                    isAnElementOf(counted, container);
            case Quantity.HowManyDifferentMeet(DecisionSubject counted, DecisionSubject _,
                                               var meeting) -> isAnElementOf(counted, container)
                    || meeting.statement().mayTurnOnAnElementOf(container);
            case Quantity.HowManyDifferentAcross(DecisionSubject counted, DecisionSubject _) ->
                    isAnElementOf(counted, container);
            case Quantity.HowManyDifferentBelow below ->
                    isAnElementOf(new DecisionSubject.AnInput(below.root()), container)
                            || isAnElementOf(new DecisionSubject.AnInput(below.map()), container);
            case Quantity.SumOver(DecisionSubject summed, Quantity each) ->
                    isAnElementOf(summed, container) || mayBeAnElementOf(each, container);
            case Quantity.RemainderOfADividend(var _, var dividend, var _) ->
                    dividend.coefs().keySet().stream().anyMatch(term -> isAnElementOf(
                            new DecisionSubject.AnInput(term.subjectPath()), container));
            case Quantity.RemainderByAnInput remainder -> remainder.operands().stream()
                    .anyMatch(term -> isAnElementOf(
                            new DecisionSubject.AnInput(term.subjectPath()), container));
            case Quantity.ProductOfTwo product -> product.factors().stream()
                    .anyMatch(term -> isAnElementOf(
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

        @Override
        public int hashCode() {
            return key.hashCode();
        }

        public Compared(Relation relation, boolean holds) {
            this(relation, holds, null);
        }

        public Compared {
            if (relation == null) {
                throw new IllegalArgumentException("a comparison states some relation");
            }
            if (ofCounts(relation) != null) {
                throw new IllegalArgumentException("counts held against nought are whether some"
                        + " element meets what is counted, and are written as that: " + relation);
            }
            key = (holds ? "" : "!") + relation;
        }

        /** The spelling of the relation held, whichever way round this is: one for one relation. */
        public String heldKey() {
            return holds ? key : key.substring(1);
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

        @Override
        public int hashCode() {
            return key.hashCode();
        }

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

        @Override
        public int hashCode() {
            return key.hashCode();
        }

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

        @Override
        public int hashCode() {
            return key.hashCode();
        }

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

        @Override
        public int hashCode() {
            return key.hashCode();
        }

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
     * @param container where the container stands: a position of the input, whose elements the row
     *                  writes, or a list a dependency answered, whose elements the answer is
     *                  composed with
     * @param position  a place under the container's element, which an element is told apart
     *                  from the others by
     * @param key       spelled from the rest when it is made, whatever is handed in
     */
    record LastToHold(DecisionSubject container, DecisionSubject position, boolean holds,
                      String key) implements Proposition {

        @Override
        public int hashCode() {
            return key.hashCode();
        }

        public LastToHold(DecisionSubject container, DecisionSubject position, boolean holds) {
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
     * What {@code states}, read only where {@code answers} holds: where it does not, an operation
     * the statement is read through answers nothing, and the run stops before the statement comes
     * out either way. Made through {@link #whereItAnswers}.
     *
     * <p>Holds where both do, and its denial is the denial of {@code states} where {@code answers}
     * holds — not the denial of both, which would say that a run which stopped came out the other
     * way. {@code answers} is where the statement is about anything at all, and so never one of
     * its lines: a row where it fails is no row of either side.
     *
     * @param key spelled from the parts' own when it is made, whatever is handed in
     */
    record WhereItAnswers(Proposition answers, Proposition states, String key)
            implements Proposition {

        @Override
        public int hashCode() {
            return key.hashCode();
        }

        public WhereItAnswers(Proposition answers, Proposition states) {
            this(answers, states, null);
        }

        public WhereItAnswers {
            if (answers == null || states == null) {
                throw new IllegalArgumentException("a statement is read somewhere, of something");
            }
            key = "where " + answers.key() + " [" + states.key() + "]";
        }

        @Override
        public Proposition denied() {
            return whereItAnswers(answers, states.denied());
        }
    }

    /**
     * Every part holding. Made through {@link #all}.
     *
     * @param key spelled from the parts' own when it is made, whatever is handed in
     */
    record All(List<Proposition> parts, String key) implements Proposition {

        @Override
        public int hashCode() {
            return key.hashCode();
        }

        /**
         * Both components, the spelling first. The parts are a tree as deep as the conjunctions
         * inside one another, and two propositions that differ almost always differ in what they
         * spell, which a string's hash says before a character is compared.
         */
        @Override
        public boolean equals(Object other) {
            return this == other || (other instanceof All that
                    && key.hashCode() == that.key.hashCode() && key.equals(that.key)
                    && parts.equals(that.parts));
        }

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
            return SharedPropositions.denied(this,
                    () -> any(parts.stream().map(Proposition::denied).toList()));
        }
    }

    /**
     * Some part holding. Made through {@link #any}.
     *
     * @param key spelled from the parts' own when it is made, whatever is handed in
     */
    record Any(List<Proposition> parts, String key) implements Proposition {

        @Override
        public int hashCode() {
            return key.hashCode();
        }

        /** Both components, the spelling first, as {@link All} compares them. */
        @Override
        public boolean equals(Object other) {
            return this == other || (other instanceof Any that
                    && key.hashCode() == that.key.hashCode() && key.equals(that.key)
                    && parts.equals(that.parts));
        }

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

        /** Every part failing — which {@link #all} keeps as the cases of a condition where the
         *  parts are cases of one ({@link #byTheCases}). */
        @Override
        public Proposition denied() {
            return SharedPropositions.denied(this,
                    () -> all(parts.stream().map(Proposition::denied).toList()));
        }
    }

    /**
     * {@code conjuncts} as the cases of the first condition some of them say what follows from,
     * or null where none does.
     *
     * <p>A conjunct one part of which is the denial of a condition {@code X} says what holds
     * where {@code X} does — {@code ¬X ∨ A} is {@code X → A} — and one a part of which is {@code X}
     * says what holds where it does not. Where both are among them, {@code (¬X ∨ A) ∧ (X ∨ B) ∧ R}
     * holds exactly where {@code ((X ∧ A) ∨ (¬X ∧ B)) ∧ R} does: one statement, which an
     * {@code if} on {@code X}, the denial of the cases of {@code X} and the two implications
     * written out each state, and which comes to one proposition whichever of them wrote it. Kept
     * as the cases of {@code X}, several such statements are chosen once per case of it, where
     * each implication apart would be a choice of its own, every combination of which is a way.
     *
     * <p>Only of a condition whose denial holds wherever it fails ({@link
     * #deniedWhereverItFails}): the cases of one that may answer nothing, or hold on one
     * application and fail on another, are not every row. A conjunct with both {@code X} and its
     * denial among its parts holds on every row, and is left out. Two conjuncts that are each no
     * more than {@code X} and its denial are left as they stand: what is said of them is that the
     * two are asked at once, which is a reader's to say and not something to be worked out here.
     */
    private static Proposition byTheCases(List<Proposition> conjuncts) {
        List<Set<String>> partsOfEach = new ArrayList<>(conjuncts.size());
        Set<String> anywhere = new HashSet<>();
        for (Proposition conjunct : conjuncts) {
            Set<String> keys = new HashSet<>();
            disjunctsOf(conjunct).forEach(each -> keys.add(each.key()));
            partsOfEach.add(keys);
            anywhere.addAll(keys);
        }
        for (Proposition conjunct : conjuncts) {
            for (Proposition against : disjunctsOf(conjunct)) {
                Proposition condition = against.denied();
                if (!anywhere.contains(condition.key()) || !deniedWhereverItFails(condition)) {
                    continue;
                }
                List<Proposition> whereItHolds = new ArrayList<>();
                List<Proposition> whereItFails = new ArrayList<>();
                List<Proposition> rest = new ArrayList<>();
                boolean saysMore = false;
                boolean everyRow = false;
                for (int at = 0; at < conjuncts.size(); at++) {
                    Proposition each = conjuncts.get(at);
                    boolean holding = partsOfEach.get(at).contains(against.key());
                    boolean failing = partsOfEach.get(at).contains(condition.key());
                    if (holding && failing) {
                        everyRow = true;
                    } else if (holding) {
                        whereItHolds.add(without(each, against));
                        saysMore |= each instanceof Any;
                    } else if (failing) {
                        whereItFails.add(without(each, condition));
                        saysMore |= each instanceof Any;
                    } else {
                        rest.add(each);
                    }
                }
                if (whereItHolds.isEmpty() || whereItFails.isEmpty() || !saysMore) {
                    if (everyRow) {
                        return all(conjuncts.stream().filter(each -> !(disjunctsOf(each)
                                .contains(against) && disjunctsOf(each).contains(condition)))
                                .toList());
                    }
                    continue;
                }
                rest.add(any(List.of(all(List.of(condition, all(whereItHolds))),
                        all(List.of(against, all(whereItFails))))));
                return all(rest);
            }
        }
        return null;
    }

    private static List<Proposition> disjunctsOf(Proposition stated) {
        return stated instanceof Any any ? any.parts() : List.of(stated);
    }

    /** What {@code stated} holds beside {@code part}, which fails where nothing else holds. */
    private static Proposition without(Proposition stated, Proposition part) {
        return any(disjunctsOf(stated).stream()
                .filter(each -> !each.key().equals(part.key())).toList());
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

        @Override
        public int hashCode() {
            return key.hashCode();
        }

        public Some(DecisionSubject container, Proposition ofTheElement, boolean holds) {
            this(container, ofTheElement, holds, null);
        }

        public Some {
            if (container == null || ofTheElement == null) {
                throw new IllegalArgumentException("a quantifier is over some container");
            }
            if (quantifiesOver(container, ofTheElement)) {
                throw new IllegalArgumentException("a quantifier over " + container
                        + " says of its element another quantifier over it, which would read two"
                        + " elements as one: " + ofTheElement);
            }
            // Some element meeting a statement that answers nothing on some elements is no
            // statement of what an operation over them answers: that turns on which element a run
            // reaches first, which is said where the operation is read.
            if (holdsAnAnswering(ofTheElement)) {
                throw new IllegalArgumentException("a quantifier over " + container + " is of a"
                        + " statement answering on every element: " + ofTheElement);
            }
            key = (holds ? "some " : "no ") + container + " [" + ofTheElement.key() + "]";
        }

        /**
         * Whether {@code stated} quantifies {@code container} somewhere in it: what a reader that
         * would put {@code stated} inside a quantifier over {@code container} asks first, since
         * the two elements would be one subject there.
         *
         * <p>The container as {@code stated} names it where it stands, and not its spelling: what a
         * search asks of each node it reaches names the places under the node it was written of,
         * and those are the places under the node reached ({@link SomeReachable}). Where the
         * search starts below the node it was written of, no node it reaches is that node, so a
         * quantifier there over a container under it is over another container, whatever it is
         * spelled. Where it starts at that node, the node itself is reached, and the container
         * is the one spelled. What the search says of the node it starts at having none below is
         * said of that node as it stands, and its containers are the ones spelled.
         */
        public static boolean quantifiesOver(DecisionSubject container, Proposition stated) {
            return quantifiesOverInside(container, stated, List.of());
        }

        /** {@link #quantifiesOver}, inside searches written of each of {@code rebound}. */
        private static boolean quantifiesOverInside(DecisionSubject container, Proposition stated,
                                                    List<TermPath> rebound) {
            return switch (stated) {
                case Some some -> (some.container.equals(container)
                        && !reboundBy(some.container, rebound))
                        || quantifiesOverInside(container, some.ofTheElement, rebound);
                case All all -> all.parts().stream()
                        .anyMatch(part -> quantifiesOverInside(container, part, rebound));
                case Any any -> any.parts().stream()
                        .anyMatch(part -> quantifiesOverInside(container, part, rebound));
                case SomeReachable reached -> {
                    List<TermPath> inside = rebound;
                    if (reached.startsBelowWhereItWasWritten()) {
                        inside = new ArrayList<>(rebound);
                        inside.add(reached.writtenAt());
                    }
                    yield quantifiesOverInside(container, reached.atANode(), inside)
                            || reached.noneBelow()
                                    .filter(each -> quantifiesOverInside(container, each, rebound))
                                    .isPresent();
                }
                case OnAnApplication applied -> applied.each().stream()
                        .anyMatch(each -> quantifiesOverInside(container, each, rebound));
                case SoManyHold counted -> counted.statements().stream()
                        .anyMatch(each -> quantifiesOverInside(container, each, rebound));
                case WhereItAnswers where ->
                        quantifiesOverInside(container, where.answers(), rebound)
                                || quantifiesOverInside(container, where.states(), rebound);
                case Always _, Compared _, Truth _, InCases _, Present _, SameValue _,
                     LastToHold _, Carried _, Unread _ -> false;
            };
        }

        /** Whether {@code container} is a place under the node a search around it was written
         *  of, which names the place under each node the search reaches. */
        private static boolean reboundBy(DecisionSubject container, List<TermPath> rebound) {
            return container instanceof DecisionSubject.AnInput(TermPath at)
                    && rebound.stream().anyMatch(at::isAtOrUnder);
        }

        @Override
        public Proposition denied() {
            return new Some(container, ofTheElement, !holds);
        }

        /** This quantifier with the parts it asks of its element, spelled once. */
        public ElementAsked elementAsked() {
            return new ElementAsked(this, switch (ofTheElement) {
                case All all -> all.parts().stream().map(Proposition::key)
                        .collect(Collectors.toUnmodifiableSet());
                case Always(boolean always) -> always ? Set.of() : Set.of(ofTheElement.key());
                // One part, whatever it says: two spelled alike are one statement.
                case Compared _, Truth _, InCases _, Present _, SameValue _, LastToHold _, Any _,
                     Some _, Carried _, SomeReachable _, Unread _, OnAnApplication _,
                     SoManyHold _, WhereItAnswers _ -> Set.of(ofTheElement.key());
            });
        }

        /**
         * A quantifier and the spellings of the parts it asks of its element, each once.
         *
         * @param quantifier the quantifier
         * @param parts      what it asks of its element, part by part; none where it asks nothing
         */
        public record ElementAsked(Some quantifier, Set<String> parts) {

            public ElementAsked {
                Objects.requireNonNull(quantifier, "the parts are some quantifier's");
                parts = Set.copyOf(parts);
            }

            /**
             * Whether {@code other} holds wherever this does, and is not the same statement: both
             * held, over one container, and every part {@code other} asks of its element one this
             * asks of its own, with more besides. An element meeting this meets {@code other}, so
             * the container holds one.
             *
             * <p>Read off the parts as they are written and nothing more: a part {@code other}
             * asks that this asks only in other words is no part this was seen to ask, and the
             * answer is no. And never both ways round, since each asks more than the other.
             *
             * <p>Asked of two quantifiers standing side by side in one statement, where a
             * container and a part spelled alike are one container and one part. Inside a search
             * a place is named by the node the search was written of ({@link SomeReachable}), so
             * a quantifier there is not compared with one outside it by how they are spelled.
             */
            public boolean holdsOnlyWhere(ElementAsked other) {
                return quantifier.holds && other.quantifier.holds
                        && quantifier.container.equals(other.quantifier.container)
                        && parts.size() > other.parts.size() && parts.containsAll(other.parts);
            }
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

        @Override
        public int hashCode() {
            return key.hashCode();
        }

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

        @Override
        public int hashCode() {
            return key.hashCode();
        }

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
            if (holdsAnAnswering(atANode)
                    || noneBelow.filter(Proposition::holdsAnAnswering).isPresent()) {
                throw new IllegalArgumentException("a search is of a statement answering on every"
                        + " node: " + atANode);
            }
            key = (holds ? "reachable " : "unreachable ") + at + " from " + writtenAt + " through "
                    + through + " [" + atANode.key() + "]"
                    + noneBelow.map(none -> " none below [" + none.key() + "]").orElse("");
        }

        @Override
        public Proposition denied() {
            return new SomeReachable(at, writtenAt, through, atANode, noneBelow, !holds);
        }

        /**
         * Whether the search starts below the node {@code atANode} is written of, so that no node
         * it reaches is that node: the places {@code atANode} names under it are then places
         * under other nodes.
         */
        public boolean startsBelowWhereItWasWritten() {
            return at.isAtOrUnder(writtenAt) && !at.equals(writtenAt);
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

        @Override
        public int hashCode() {
            return key.hashCode();
        }

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

        @Override
        public int hashCode() {
            return key.hashCode();
        }

        /** Both components, the spelling first, as {@link All} compares them. */
        @Override
        public boolean equals(Object other) {
            return this == other || (other instanceof OnAnApplication that
                    && key.hashCode() == that.key.hashCode() && key.equals(that.key)
                    && each.equals(that.each));
        }

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
            return SharedPropositions.denied(this,
                    () -> onAnApplication(each.stream().map(Proposition::denied).toList()));
        }
    }

    /**
     * How many of {@code statements} hold, each weighed as many times as it was written, being one
     * of the counts {@code admitted}. Made through {@link #compared(Relation, boolean)}, and
     * only where the choices of which of them hold are more than the statements are.
     *
     * <p>The statements and the count, and not the choices. Written out, a choice names every
     * statement — each one chosen holding and, for a count that admits no more, each other one
     * failing — so exactly one of {@code n} is {@code n} choices of {@code n} statements each, and
     * exactly four of eight is seventy. Held here, each statement is held once; a reader that
     * reads a count reads this, and one that needs the choices is handed them through {@link
     * CountsWrittenOut}, held to how many they are and how many parts every count it is handed
     * comes to together.
     *
     * <p>Denied, it is the count being one of the others. No statement is denied by that, and no
     * choice is made.
     *
     * <p>Nothing is supposed of how the statements stand to one another. A statement and its denial
     * can both be among them, and then no choice holds both; which counts some choice comes to is
     * the choices', and not anything worked out from the weights alone.
     *
     * @param statements each kept once, in the order of their keys
     * @param weights    how many times each of {@code statements} was written, in the same order
     * @param admitted   the counts this holds at, rising — none of them every count there is, and
     *                   not none
     * @param key        spelled from the rest when it is made, whatever is handed in
     */
    record SoManyHold(List<Proposition> statements, List<Integer> weights, List<Integer> admitted,
                      String key) implements Proposition {

        @Override
        public int hashCode() {
            return key.hashCode();
        }

        /** Every component, the spelling first, as {@link All} compares them. */
        @Override
        public boolean equals(Object other) {
            return this == other || (other instanceof SoManyHold that
                    && key.hashCode() == that.key.hashCode() && key.equals(that.key)
                    && statements.equals(that.statements) && weights.equals(that.weights)
                    && admitted.equals(that.admitted));
        }

        public SoManyHold(List<Proposition> statements, List<Integer> weights,
                          List<Integer> admitted) {
            this(statements, weights, admitted, null);
        }

        public SoManyHold {
            statements = List.copyOf(statements);
            weights = List.copyOf(weights);
            admitted = List.copyOf(admitted);
            if (statements.isEmpty() || statements.size() != weights.size()) {
                throw new IllegalArgumentException("a count is of some statements, each weighed: "
                        + statements + " " + weights);
            }
            if (statements.stream().anyMatch(Proposition::holdsAnAnswering)) {
                throw new IllegalArgumentException("a count is of statements answering on every"
                        + " row: " + statements);
            }
            for (int at = 1; at < statements.size(); at++) {
                if (statements.get(at - 1).key().compareTo(statements.get(at).key()) >= 0) {
                    throw new IllegalArgumentException("statements are kept once, in the order of"
                            + " their keys: " + statements);
                }
            }
            if (weights.stream().anyMatch(weight -> weight < 1)) {
                throw new IllegalArgumentException("a statement counted is written at least once: "
                        + weights);
            }
            int all = weights.stream().mapToInt(Integer::intValue).sum();
            if (admitted.isEmpty() || admitted.size() > all) {
                throw new IllegalArgumentException("a count admitted at none or at every count is"
                        + " no count of statements: " + admitted);
            }
            for (int at = 0; at < admitted.size(); at++) {
                if (admitted.get(at) < 0 || admitted.get(at) > all
                        || (at > 0 && admitted.get(at - 1) >= admitted.get(at))) {
                    throw new IllegalArgumentException("the counts admitted rise, from nought to "
                            + all + ": " + admitted);
                }
            }
            StringBuilder spelled = new StringBuilder("so many hold").append(admitted).append(" of [");
            for (int at = 0; at < statements.size(); at++) {
                spelled.append(at == 0 ? "" : ", ").append(weights.get(at)).append('*')
                        .append(statements.get(at).key());
            }
            key = spelled.append(']').toString();
        }

        /** How many the statements come to where every one of them holds. */
        public int weight() {
            return weights.stream().mapToInt(Integer::intValue).sum();
        }

        /**
         * A count of {@code statements}, each weighed as many times as {@code weights} says, being
         * one of {@code admitted} — with what the statements say of themselves taken out.
         *
         * <p>A statement that holds on every row adds its weight to every count, and one that fails
         * on every row adds none, so neither is counted: the counts admitted are the ones left once
         * the first are taken from them. Two statements written alike are one statement weighed
         * twice. What is left is the count again where it is a count, and otherwise what it comes
         * to for every row — a count admitted at none of the counts there are, or at every one,
         * which {@code SoManyHold} is not made for.
         *
         * @param admitted the counts admitted, rising; may reach past what the statements come to
         */
        public static Proposition counting(List<Proposition> statements, List<Integer> weights,
                                           List<Integer> admitted) {
            SortedMap<String, Proposition> kept = new TreeMap<>();
            Map<String, Integer> weighed = new HashMap<>();
            int always = 0;
            for (int at = 0; at < statements.size(); at++) {
                Proposition statement = statements.get(at);
                if (statement instanceof Always(boolean holds)) {
                    always += holds ? weights.get(at) : 0;
                    continue;
                }
                kept.putIfAbsent(statement.key(), statement);
                weighed.merge(statement.key(), weights.get(at), Integer::sum);
            }
            int all = weighed.values().stream().mapToInt(Integer::intValue).sum();
            List<Integer> counts = new ArrayList<>();
            for (int count : admitted) {
                int left = count - always;
                if (left >= 0 && left <= all) {
                    counts.add(left);
                }
            }
            if (counts.isEmpty()) {
                return new Always(false);
            }
            if (counts.size() == all + 1) {
                return new Always(true);
            }
            List<Integer> merged = kept.keySet().stream().map(weighed::get).toList();
            Boolean settled = settledByTheWeights(merged, counts);
            if (settled != null) {
                return new Always(settled);
            }
            return SharedPropositions.shared(new SoManyHold(List.copyOf(kept.values()), merged,
                    counts));
        }

        /**
         * What the weights alone say of a count admitted at {@code admitted}, whatever the
         * statements are: false where no set of them weighs a number it admits, true where every
         * set does, and null where some do and some do not.
         *
         * <p>Statements weighing two each come to an even number however they come out, so
         * admitting one of them is admitting nothing. A count like that is made — the denial of
         * one admitting every even number is — and is a fact of the model and not of any row.
         *
         * @param weights  how many times each statement was written
         * @param admitted the counts admitted
         */
        public static Boolean settledByTheWeights(List<Integer> weights, List<Integer> admitted) {
            int all = weights.stream().mapToInt(Integer::intValue).sum();
            boolean[] weighs = new boolean[all + 1];
            weighs[0] = true;
            for (int weight : weights) {
                for (int sum = all; sum >= weight; sum--) {
                    weighs[sum] |= weighs[sum - weight];
                }
            }
            boolean some = false;
            boolean other = false;
            for (int sum = 0; sum <= all; sum++) {
                if (weighs[sum]) {
                    if (admitted.contains(sum)) {
                        some = true;
                    } else {
                        other = true;
                    }
                }
            }
            return (some && other) ? null : some;
        }

        /**
         * This count over {@code each} of its statements instead — itself where none changed. What
         * a statement is replaced by is the count's to count, so a statement that comes out the
         * same as another is weighed with it ({@link #counting}).
         */
        public Proposition mapped(UnaryOperator<Proposition> each) {
            List<Proposition> out = new ArrayList<>(statements.size());
            boolean changed = false;
            for (Proposition statement : statements) {
                Proposition replaced = each.apply(statement);
                changed |= replaced != statement;
                out.add(replaced);
            }
            return changed ? counting(out, weights, admitted) : this;
        }

        @Override
        public Proposition denied() {
            List<Integer> others = new ArrayList<>();
            for (int count = 0; count <= weight(); count++) {
                if (Collections.binarySearch(admitted, count) < 0) {
                    others.add(count);
                }
            }
            return SharedPropositions.denied(this,
                    () -> SharedPropositions.shared(new SoManyHold(statements, weights, others)));
        }

        /** Which way a count comes out, as far as what each statement can come out as says. */
        public enum ComesOut {
            /** It holds however the statements come out. */
            HOLDING,
            /** It fails however the statements come out. */
            FAILING,
            /** Some way the statements come out holds it and some way fails it. */
            EITHER_WAY
        }

        /**
         * Which way this comes out, where each of {@link #statements} can hold as {@code mayHold}
         * says and fail as {@code mayFail} says, in the same order.
         *
         * <p>The counts the statements come to, each taken apart from the others, are every count
         * they do come to and maybe more: two statements that cannot hold together are counted
         * here as though they could. So it comes out one way only where every one of those counts
         * says so — never one way where the statements could bring it out the other.
         */
        public ComesOut comesOut(List<Boolean> mayHold, List<Boolean> mayFail) {
            boolean[] comesTo = new boolean[weight() + 1];
            comesTo[0] = true;
            for (int one = 0; one < statements.size(); one++) {
                int weighs = weights.get(one);
                boolean[] next = new boolean[comesTo.length];
                for (int count = 0; count < comesTo.length; count++) {
                    if (comesTo[count]) {
                        next[count] |= mayFail.get(one);
                        if (mayHold.get(one)) {
                            next[count + weighs] = true;
                        }
                    }
                }
                comesTo = next;
            }
            boolean holding = false;
            boolean failing = false;
            for (int count = 0; count < comesTo.length; count++) {
                if (comesTo[count]) {
                    if (Collections.binarySearch(admitted, count) >= 0) {
                        holding = true;
                    } else {
                        failing = true;
                    }
                }
            }
            return holding && failing ? ComesOut.EITHER_WAY
                    : holding ? ComesOut.HOLDING : ComesOut.FAILING;
        }

        /**
         * Some one of the choices of which statements hold that put the count where this admits it,
         * written out, with how many parts they come to — or none, where they are more than one
         * condition is read in ({@link CompositionBudget#READINGS_OF_ONE_CONDITION}) or written out
         * come to more parts than {@link CompositionBudget#PARTS_THE_CHOICES_OF_A_COUNT_COME_TO},
         * and which of the two.
         *
         * <p>What holds exactly where this does, for a reader that can read a disjunction of
         * conjunctions and not a count. Written out once for the count, and handed to a reader
         * only through {@link CountsWrittenOut}, which holds the reader to what every count it is
         * handed comes to together.
         */
        WhichOfThemHold.Written writtenForAReader() {
            return SharedPropositions.choices(this, this::writtenOutForAReader);
        }

        /** The choices written out no further than {@link #writtenForAReader} says, each time it
         *  is asked. */
        private WhichOfThemHold.Written writtenOutForAReader() {
            return WhichOfThemHold.of(this).written(CompositionBudget.READINGS_OF_ONE_CONDITION,
                    CompositionBudget.PARTS_THE_CHOICES_OF_A_COUNT_COME_TO);
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
                : SharedPropositions.shared(new OnAnApplication(List.copyOf(kept.values())));
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
        List<WhyUnread> stops = new ArrayList<>(1);
        stopsIn(stated, stops, true);
        return stops.isEmpty() ? null : stops.getFirst();
    }

    /** Why each part of {@code stated} nothing read stopped, in the order its parts are kept. */
    static List<WhyUnread> stopsIn(Proposition stated) {
        List<WhyUnread> out = new ArrayList<>();
        stopsIn(stated, out, false);
        return List.copyOf(out);
    }

    /** Each stop in {@code stated} added to {@code into} in the order its parts are kept, or the
     *  first alone where {@code first}; whether one was added. */
    private static boolean stopsIn(Proposition stated, List<WhyUnread> into, boolean first) {
        return switch (stated) {
            case Unread unread -> into.add(unread.why());
            case All _, Any _, OnAnApplication _, SoManyHold _, Some _, SomeReachable _,
                 WhereItAnswers _ -> stopsIn(stated.partsHeld(), into, first);
            case Always _, Compared _, Truth _, InCases _, Present _, SameValue _,
                 LastToHold _, Carried _ -> false;
        };
    }

    private static boolean stopsIn(List<Proposition> parts, List<WhyUnread> into, boolean first) {
        boolean added = false;
        for (Proposition part : parts) {
            added |= stopsIn(part, into, first);
            if (added && first) {
                return true;
            }
        }
        return added;
    }

    /**
     * Whether {@code stated} says of some element that it is the last of those holding a value —
     * which a map filed from a list says of the entry under a key.
     */
    static boolean saysTheLastToHold(Proposition stated) {
        return !stated.lastsToHold().isEmpty();
    }

    /**
     * Every statement inside this of which element is the last of those holding a value, in the
     * order they are met.
     *
     * <p>Each is a distinction of its own: a statement resting on two maps, each filed from a list,
     * rests on two orders, and reading one the other way round leaves the other as it is. A reader
     * that asks what an order decides asks it of one of these and not of the statement they are
     * parts of.
     */
    default List<LastToHold> lastsToHold() {
        if (this instanceof LastToHold last) {
            return List.of(last);
        }
        return partsHeld().stream().flatMap(part -> part.lastsToHold().stream()).toList();
    }

    /**
     * Whether {@code stated} is, or holds, a search from a node for some node below it meeting
     * something.
     */
    static boolean saysASearchReachesBelow(Proposition stated) {
        return switch (stated) {
            case SomeReachable _ -> true;
            case All _, Any _, OnAnApplication _, SoManyHold _, Some _, WhereItAnswers _ ->
                    stated.partsHeld().stream().anyMatch(Proposition::saysASearchReachesBelow);
            case Always _, Compared _, Truth _, InCases _, Present _, SameValue _, Unread _,
                 Carried _, LastToHold _ -> false;
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
            case Always _, Unread _, Carried _ -> false;
            case LastToHold last -> last.container() instanceof DecisionSubject.AnAnswer;
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
            case All _, Any _, OnAnApplication _, SoManyHold _, SomeReachable _,
                 WhereItAnswers _ ->
                    stated.partsHeld().stream().anyMatch(Proposition::aboutAnAnswer);
            case Some some -> some.container() instanceof DecisionSubject.AnAnswer
                    || some.partsHeld().stream().anyMatch(Proposition::aboutAnAnswer);
        };
    }

    /** Whether {@code quantity} is about what a dependency answered: a number of an answer, or a
     *  number over a container an answer holds or over elements asked something of one. */
    static boolean anAnswerIn(Quantity quantity) {
        return switch (quantity) {
            case DecisionAtom.OfAnAnswer _, DecisionAtom.TakenOfAnAnswer _,
                 DecisionAtom.ComputedOverAnAnswer _ -> true;
            case DecisionAtom.OfTheInput _, Quantity.OfABinding _,
                 Quantity.CodePointsOfAPiece _, Quantity.RemainderOfADividend _,
                 Quantity.RemainderByAnInput _, Quantity.ProductOfTwo _,
                 Quantity.WhatAnOperationAnswers _, Quantity.HowManyCarried _,
                 Quantity.APieceOf _, Quantity.IsAmongThePieces _ -> false;
            case Quantity.HowManyMeet count -> count.container() instanceof DecisionSubject.AnAnswer
                    || aboutAnAnswer(count.ofTheElement());
            case Quantity.HowManyHold held -> held.each().stream()
                    .anyMatch(Proposition::aboutAnAnswer);
            case Quantity.HowManyDifferent different ->
                    different.container() instanceof DecisionSubject.AnAnswer
                            || different.ofTheElement() instanceof DecisionSubject.AnAnswer;
            case Quantity.HowManyDifferentMeet different ->
                    different.container() instanceof DecisionSubject.AnAnswer
                            || different.ofTheElement() instanceof DecisionSubject.AnAnswer
                            || aboutAnAnswer(different.meeting().statement());
            case Quantity.HowManyDifferentAcross across ->
                    across.container() instanceof DecisionSubject.AnAnswer
                            || across.ofTheOccurrence() instanceof DecisionSubject.AnAnswer;
            case Quantity.HowManyDifferentBelow _ -> false;
            case Quantity.SumOver sum -> sum.container() instanceof DecisionSubject.AnAnswer
                    || anAnswerIn(sum.ofTheElement());
        };
    }

    /**
     * {@code relation} held or failing as {@code holds}, written as what it comes to where it holds
     * counts of elements against nought ({@link #ofCounts}), or, where it holds a count of
     * statements about values written out, as which of them hold ({@link WhichOfThemHold#stated}).
     */
    static Proposition compared(Relation relation, boolean holds) {
        Proposition counted = ofCounts(relation);
        if (counted == null) {
            WhichOfThemHold choosing = WhichOfThemHold.of(relation);
            if (choosing != null) {
                counted = choosing.stated();
            }
        }
        Proposition held = counted != null ? counted : new Compared(relation, true);
        return holds ? held : held.denied();
    }

    /**
     * What a relation over counts of elements meeting something, each weighed above nought, says,
     * where that is whether some element of one of them meets what it counts, or the same whatever
     * is counted — or null where it says how many.
     *
     * <p>A count is never fewer than none and comes to none exactly where no element meets what is
     * counted. So {@code count >= 1}, {@code count > 0} and {@code count /= 0} are some element
     * meeting it, {@code count == 0} and {@code count < 1} none doing so, and {@code count >= 0}
     * every row: one statement each, made one proposition whichever was written, and the same one
     * the element that witnesses a filter's answer holding something is read as. A relation that
     * says how many beyond that — exactly one, two or more — is kept as the relation.
     *
     * <p>A sum of counts weighed above nought is above nought exactly where one of them is, and is
     * then at least the least weight. So it held at or past nought and no further than that weight
     * is some element of one of them meeting what it counts — {@code #xs + #ys >= 1} is one of xs
     * or one of ys — and held to nought is none of them doing so. A weight below nought would let
     * one count make up for another, and the relation is kept.
     */
    private static Proposition ofCounts(Relation relation) {
        if (!(relation instanceof Relation.Affine(LinearForm<Quantity> form, Rel rel))
                || form.coefs().isEmpty()) {
            return null;
        }
        ExactRatio least = null;
        for (Map.Entry<Quantity, ExactRatio> each : form.coefs().entrySet()) {
            if (!(each.getKey() instanceof Quantity.HowManyMeet) || each.getValue().signum() <= 0) {
                return null;
            }
            least = least == null || each.getValue().compareTo(least) < 0 ? each.getValue() : least;
        }
        // Σ a·count + k rel 0 with every a positive, in steps of the least a: Σ (a/least)·count
        // rel t, which is nought or one step and more wherever it is above nought.
        ExactAnswer<ExactRatio> at = form.constant().negated().dividedBy(least);
        if (!(at instanceof ExactAnswer.Held<ExactRatio>(ExactRatio t))) {
            return null;
        }
        int againstNought = t.signum();
        boolean atMostOne = t.compareTo(ExactRatio.ONE) <= 0;
        boolean belowOne = t.compareTo(ExactRatio.ONE) < 0;
        return switch (rel) {
            case GE -> againstNought <= 0 ? new Always(true) : atMostOne ? someMeets(form) : null;
            case GT -> againstNought < 0 ? new Always(true)
                    : belowOne ? someMeets(form) : null;
            case EQ -> againstNought < 0 || (!t.isWhole() && inWholeSteps(form, least))
                    ? new Always(false)
                    : againstNought == 0 ? someMeets(form).denied() : null;
            case LE, LT, NE -> throw new IllegalStateException(
                    "a relation is written under the canonical one of it and its denial");
        };
    }

    /**
     * Whether {@code relation} is counts held against nought, which is written as whether some
     * element of one of them meets what it counts, or the same whatever is counted ({@link
     * #ofCounts}) — so that no relation of its own is left.
     */
    public static boolean comesToWhetherAnyMeets(Relation relation) {
        return ofCounts(relation) != null;
    }

    /** Some element of one of the containers {@code counts} counts meeting what it counts. */
    private static Proposition someMeets(LinearForm<Quantity> counts) {
        List<Proposition> meeting = new ArrayList<>(counts.coefs().size());
        for (Quantity count : counts.coefs().keySet()) {
            if (count instanceof Quantity.HowManyMeet meets) {
                meeting.add(meets.someMeets());
            }
        }
        return any(meeting);
    }

    /**
     * Whether every weight {@code counts} has is a whole number of {@code step}s, so that the sum
     * comes only to whole steps: two of each, held equal to three, is never.
     */
    private static boolean inWholeSteps(LinearForm<Quantity> counts, ExactRatio step) {
        return counts.coefs().values().stream().allMatch(weight ->
                weight.dividedBy(step) instanceof ExactAnswer.Held<ExactRatio>(ExactRatio steps)
                        && steps.isWhole());
    }

    /**
     * Every one of {@code parts} holding: what holds of all of them, with a part that always holds
     * left out, one that never does settling it, and each part kept once in one order.
     */
    static Proposition all(List<Proposition> parts) {
        return joined(parts, true);
    }

    /**
     * {@code states} read only where {@code answers} holds — {@code states} itself where it answers
     * on every row.
     */
    static Proposition whereItAnswers(Proposition answers, Proposition states) {
        if (answers instanceof Always(boolean everywhere) && everywhere) {
            return states;
        }
        // Where it answers is one region however many operations it was said of.
        return states instanceof WhereItAnswers(Proposition inner, Proposition stated, String _)
                ? new WhereItAnswers(all(List.of(answers, inner)), stated)
                : new WhereItAnswers(answers, states);
    }

    /**
     * What a statement read through an operation no run gets past comes to: it answers on no row,
     * so it holds on none and fails on none, and its denial is the same. Not {@code Always(false)},
     * which fails on every row, and not an arm no run takes ({@link Derivation.NoRunTakesIt}),
     * where no run arrives: here a run arrives and the operation stops it.
     */
    static Proposition answersNowhere() {
        return new WhereItAnswers(new Always(false), new Always(false));
    }

    /** Whether {@code stated} answers on no row ({@link #answersNowhere}). */
    static boolean answersNowhere(Proposition stated) {
        return stated instanceof WhereItAnswers(Proposition answers, Proposition _, String _)
                && answers instanceof Always(boolean everywhere) && !everywhere;
    }

    /**
     * The rows {@code stated} answers on, or null where it answers on every row: where each
     * operation a part of it is read through answers ({@link WhereItAnswers}), and past that, where
     * the parts that do answer decide it without the ones that do not.
     *
     * <p>Read off what the parts state and nothing else. Which part a run works out first is not in
     * a statement, so where that decides whether a run stops, it was said where the statement was
     * made ({@link #afterIt}).
     */
    static Proposition answeredWhere(Proposition stated) {
        if (!holdsAnAnswering(stated)) {
            return null;
        }
        if (stated instanceof WhereItAnswers(Proposition answers, Proposition states, String _)) {
            Proposition inside = answeredWhere(states);
            return inside == null ? answers : all(List.of(answers, inside));
        }
        return any(List.of(stated, stated.denied()));
    }

    /**
     * The two positions of the input {@code stated} says hold one value, or null where it says
     * anything else.
     *
     * <p>Said two ways and read as one: {@link SameValue} of two positions, and the difference of
     * two positions held at nought ({@link Compared}), which is how a statement that two ordered
     * values are one is stated once a count is made of it.
     */
    public static List<TermPath> positionsHeldEqual(Proposition stated) {
        if (stated instanceof SameValue(DecisionSubject one, DecisionSubject other, boolean holds,
                var _)) {
            return holds && one instanceof DecisionSubject.AnInput(TermPath at)
                    && other instanceof DecisionSubject.AnInput(TermPath alsoAt)
                    ? List.of(at, alsoAt) : null;
        }
        if (!(stated instanceof Compared(Relation relation, boolean holds, var _))
                || !holds
                || !(relation instanceof Relation.Affine(LinearForm<Quantity> form, Rel rel))
                || rel != Rel.EQ || form.constant().signum() != 0 || form.coefs().size() != 2) {
            return null;
        }
        List<TermPath> positions = new ArrayList<>();
        List<ExactRatio> weights = new ArrayList<>();
        for (Map.Entry<Quantity, ExactRatio> each : form.coefs().entrySet()) {
            if (!(each.getKey() instanceof DecisionAtom.OfTheInput(
                    NumericTerm.ValueOf(TermPath position)))) {
                return null;
            }
            positions.add(position);
            weights.add(each.getValue());
        }
        // One minus the other, whichever way round.
        return weights.get(0).negated().compareTo(weights.get(1)) == 0
                && (weights.get(0).compareTo(ExactRatio.ONE) == 0
                        || weights.get(1).compareTo(ExactRatio.ONE) == 0) ? positions : null;
    }

    /**
     * Whether {@code stated} answers nothing on some rows: some part of it is read through an
     * operation that answers only on some ({@link WhereItAnswers}).
     */
    public static boolean mayAnswerNothing(Proposition stated) {
        return holdsAnAnswering(stated);
    }

    /**
     * The rows {@code stated} answers on, as a statement holding or failing on every row — or null
     * where it answers on every row ({@link #answeredWhere}, said with nothing in it that answers
     * nothing anywhere).
     *
     * <p>What a quantifier, a count or the way to an application is made of: each of those is of
     * statements every row answers, and {@link #answeredWhere} keeps a statement and its denial side
     * by side where the part that may answer nothing stands inside it.
     */
    public static Proposition whereItAnswersAtAll(Proposition stated) {
        if (!holdsAnAnswering(stated)) {
            return null;
        }
        // Where it answers may be written as a part and its denial side by side, which holds
        // where the part answers either way.
        if (stated instanceof WhereItAnswers(Proposition answers, Proposition states, String _)) {
            Proposition inside = whereItAnswersAtAll(states);
            return inside == null ? whereItHolds(answers)
                    : all(List.of(whereItHolds(answers), inside));
        }
        return any(List.of(whereItHolds(stated), whereItHolds(stated.denied())));
    }

    /**
     * Where {@code stated} holds, as a statement holding or failing on every row: on the rows it
     * answers on and comes out holding, and on no other. A part read through an operation that
     * answers nothing on some rows holds where the operation answers and the part holds there.
     *
     * <p>The rows it fails on are {@code whereItHolds(stated.denied())}, and the two together are
     * the rows it answers on — never every row, where something in it answers nothing.
     */
    public static Proposition whereItHolds(Proposition stated) {
        if (!holdsAnAnswering(stated)) {
            return stated;
        }
        return switch (stated) {
            case WhereItAnswers(Proposition answers, Proposition states, String _) ->
                    all(List.of(whereItHolds(answers), whereItHolds(states)));
            case All all -> all(all.parts().stream().map(Proposition::whereItHolds).toList());
            case Any any -> any(any.parts().stream().map(Proposition::whereItHolds).toList());
            case OnAnApplication applied -> onAnApplication(applied.each().stream()
                    .map(Proposition::whereItHolds).toList());
            // What one of these holds of is read on every row, by its constructor.
            case SoManyHold _, Some _, SomeReachable _ -> throw new IllegalStateException(
                    "a count or a quantifier is of statements answering on every row: " + stated);
            case Always _, Compared _, Truth _, InCases _, Present _, SameValue _, LastToHold _,
                 Carried _, Unread _ -> stated;
        };
    }

    /** Whether some part of {@code stated} answers only where an operation does. */
    private static boolean holdsAnAnswering(Proposition stated) {
        return switch (stated) {
            case WhereItAnswers _ -> true;
            // What one of these holds answers on every row, which its constructor saw to, so
            // nothing under it is walked again for each one it stands inside.
            case Some _, SoManyHold _, SomeReachable _ -> false;
            case All _, Any _, OnAnApplication _ ->
                    stated.partsHeld().stream().anyMatch(Proposition::holdsAnAnswering);
            case Always _, Compared _, Truth _, InCases _, Present _, SameValue _, LastToHold _,
                 Carried _, Unread _ -> false;
        };
    }

    /**
     * Whether the denial of {@code stated} holds on every row it fails, and on no row it holds:
     * whether the two are the two cases of one statement, as a condition and its denial are where
     * {@code c || !c} holds and {@code c && !c} does not.
     *
     * <p>Not every statement and its denial are. What is read through an operation that answers
     * only on some rows ({@link WhereItAnswers}) holds nowhere it answers nothing, and neither does
     * its denial. What a condition states on the applications of a closure ({@link
     * OnAnApplication}) holds where some application's statement does and is denied where some
     * application's denial is, so on two applications that differ both hold. And of a part nothing
     * read ({@link Unread}) nothing is known, that among the rest. A quantifier, a count and a
     * search are of statements every row answers, which their constructors saw to, and say on
     * each row how many elements or nodes meet them: a number, holding or failing.
     */
    static boolean deniedWhereverItFails(Proposition stated) {
        return switch (stated) {
            case WhereItAnswers _, OnAnApplication _, Unread _ -> false;
            case All all -> all.parts().stream().allMatch(Proposition::deniedWhereverItFails);
            case Any any -> any.parts().stream().allMatch(Proposition::deniedWhereverItFails);
            case Always _, Compared _, Truth _, InCases _, Present _, SameValue _, LastToHold _,
                 Carried _, Some _, SoManyHold _, SomeReachable _ -> true;
        };
    }

    /**
     * {@code then}, read where {@code first} answers: what a run that works {@code first} out before
     * anything {@code then} reads comes to. Where {@code first} stops, the run stops there, whatever
     * the rest would have decided — which is what a statement of both parts side by side cannot
     * say, since a part that fails decides it there.
     */
    static Proposition afterIt(Proposition first, Proposition then) {
        Proposition answered = answeredWhere(first);
        return answered == null ? then : whereItAnswers(answered, then);
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
        if (every && kept.size() > 1) {
            Proposition byCases = byTheCases(List.copyOf(kept.values()));
            if (byCases != null) {
                return byCases;
            }
        }
        return switch (kept.size()) {
            case 0 -> new Always(every);
            case 1 -> kept.firstEntry().getValue();
            default -> SharedPropositions.shared(every ? new All(List.copyOf(kept.values()))
                    : new Any(List.copyOf(kept.values())));
        };
    }
}
