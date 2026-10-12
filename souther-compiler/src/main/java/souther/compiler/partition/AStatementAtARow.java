package souther.compiler.partition;

import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.DeclaredInput;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.NumericTerms;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Rel;
import souther.compiler.numeric.UnheldNumber;
import souther.compiler.observe.ObservedValue;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

/**
 * A statement over a row's own numbers, put to rows: each relation it is over, read as the quantity
 * a row is read at, and each statement about the elements of a container, read element by element.
 *
 * <p>Read the way a line over the same quantity reads a row ({@link LinearQuantity#valuesOf}), so
 * what a row holds at a position is one answer whether a line, the place it decides, or a count of
 * the elements meeting the statement asks for it.
 *
 * <p><b>The elements of a container are read each as one reading of the row.</b> Whether some
 * element meets something, and how many do, is asked of every element the row wrote, each with that
 * element chosen ({@link BorderQuantity.Observation#eachElementOf}) — so a statement about an
 * element inside a statement about another reads the inner container under each element of the
 * outer one, and nesting is the recursion and nothing besides.
 *
 * <p><b>And a position's own value, where a part asks it whether it is true or whether there is
 * one.</b> A row writes a truth at a position as it writes a number, so whether {@code c.open}
 * holds at a row is read off what the row put there.
 */
final class AStatementAtARow {

    /** Whether the statement holds at a row, or what kept that from being read. */
    sealed interface Answer {

        /** It holds. */
        record Holds() implements Answer {}

        /** It fails, or the row holds no value one of its relations is over. */
        record Fails() implements Answer {}

        /** A number the relations are over could not be read at the row, for these reasons. */
        record CouldNotTell(Set<ReadingGap> why) implements Answer {

            /** In the order the reasons were met, which is the order a reader is told them in. */
            public CouldNotTell {
                why = Collections.unmodifiableSet(new LinkedHashSet<>(why));
            }
        }

        Answer HOLDS = new Holds();

        Answer FAILS = new Fails();
    }

    private final Proposition stated;
    private final Map<Relation, OneRelation> relations;
    private final Map<String, OverTheElements> elements;
    /** The positions a part asks of their own value: whether it is true, whether there is one. */
    private final Set<TermPath> positions;

    private AStatementAtARow(Proposition stated, Map<Relation, OneRelation> relations,
                             Map<String, OverTheElements> elements, Set<TermPath> positions) {
        this.stated = stated;
        // In the order the relations were met, which is the order their containers are found in
        // when a row is walked for them.
        this.relations = Collections.unmodifiableMap(new LinkedHashMap<>(relations));
        this.elements = Collections.unmodifiableMap(new LinkedHashMap<>(elements));
        this.positions = Collections.unmodifiableSet(new LinkedHashSet<>(positions));
    }

    /**
     * Whether a row's own values say whether {@code stated} holds at it: relations over the
     * input's own numbers, whether a position of the input is true, holds a value or is one of
     * some cases of a sum, joined, statements about the elements of a container the input holds —
     * some element meeting something, or how many do, against a number — or nothing asked at all.
     *
     * <p>Anything else is no statement a row can be asked about. Something nobody read, a truth of
     * what a dependency answered, or a count against another of the input's numbers is not settled
     * by the values a row writes, and a reader that took the statement without it would count rows
     * it says nothing about.
     */
    static boolean askable(Proposition stated) {
        return switch (stated) {
            case Proposition.Always _ -> true;
            case Proposition.Truth(DecisionSubject.AnInput _, boolean _, String _),
                 Proposition.Present(DecisionSubject.AnInput _, boolean _, String _) -> true;
            // A row names the case it wrote at a position, and that answers only cases of a sum:
            // whether an optional holds a value is asked as whether it is present.
            case Proposition.InCases(DecisionSubject.AnInput _, CasesLeft cases, boolean _,
                                     String _) ->
                    cases.atoms().stream().allMatch(Refinement.SumCase.class::isInstance);
            case Proposition.SameValue(DecisionSubject.AnInput _, DecisionSubject.AnInput _,
                                       boolean _, String _) -> true;
            case Proposition.LastToHold _ -> true;
            case Proposition.All all -> all.parts().stream().allMatch(AStatementAtARow::askable);
            case Proposition.Any any -> any.parts().stream().allMatch(AStatementAtARow::askable);
            case Proposition.Some some -> askable(some.ofTheElement());
            case Proposition.Compared compared -> switch (compared.relation()) {
                case Relation.Affine affine -> WhatTheRulesLeave.ofTheInput(affine.form()) != null
                        || (countIn(affine) instanceof Quantity.HowManyMeet count
                                && askable(count.ofTheElement()));
                case Relation.Ordered(DecisionAtom.OfTheInput(NumericTerm term), Place _, Rel _) ->
                        term.atOnePosition() != null;
                case Relation.Ordered _ -> false;
            };
            case Proposition.Truth _, Proposition.Present _, Proposition.InCases _,
                 Proposition.SameValue _, Proposition.Unread _, Proposition.OnAnApplication _,
                 Proposition.SomeReachable _ -> false;
            case Proposition.Carried carried -> throw carried.handedToAReader();
        };
    }

    /** The one count {@code affine} weighs where it weighs one and nothing else, or null. */
    static Quantity.HowManyMeet countIn(Relation.Affine affine) {
        return affine.form().coefs().size() == 1
                && affine.form().coefs().keySet().iterator().next()
                        instanceof Quantity.HowManyMeet count ? count : null;
    }

    /**
     * {@code stated}, ready to be asked of rows.
     *
     * <p>A part that is not {@link #askable} is put to no row and answered as not known wherever it
     * decides the answer: a row says nothing of what nobody read, or of what it does not write.
     * Which is what a reader of where a run got to wants — a way through an arm nothing here reads,
     * or past a closure over what a dependency answered, is a way nothing knows a row took, and not
     * a way it did not.
     *
     * @param quantities the reading of the input, which says which order each number is on
     */
    static AStatementAtARow of(Proposition stated, String behavior, Quantities quantities) {
        Map<Relation, OneRelation> relations = new LinkedHashMap<>();
        Map<String, OverTheElements> elements = new LinkedHashMap<>();
        Set<TermPath> positions = new LinkedHashSet<>();
        gather(stated, behavior, quantities, relations, elements, positions);
        return new AStatementAtARow(stated, relations, elements, positions);
    }

    private static void gather(Proposition stated, String behavior, Quantities quantities,
                               Map<Relation, OneRelation> into,
                               Map<String, OverTheElements> elements, Set<TermPath> positions) {
        switch (stated) {
            case Proposition.Always _, Proposition.LastToHold _ -> { }
            case Proposition.Truth(DecisionSubject.AnInput(TermPath at), boolean _, String _) ->
                    positions.add(at);
            case Proposition.Present(DecisionSubject.AnInput(TermPath at), boolean _, String _) ->
                    positions.add(at);
            case Proposition.InCases(DecisionSubject.AnInput(TermPath at), CasesLeft _,
                                     boolean _, String _) -> positions.add(at);
            case Proposition.SameValue(DecisionSubject.AnInput(TermPath one),
                                       DecisionSubject.AnInput(TermPath other), boolean _,
                                       String _) -> {
                positions.add(one);
                positions.add(other);
            }
            case Proposition.All all -> all.parts().forEach(part ->
                    gather(part, behavior, quantities, into, elements, positions));
            case Proposition.Any any -> any.parts().forEach(part ->
                    gather(part, behavior, quantities, into, elements, positions));
            case Proposition.Some some -> elements.computeIfAbsent(keyOf(some),
                    _ -> new OverTheElements(some.container().inputPosition(),
                            of(some.ofTheElement(), behavior, quantities)));
            case Proposition.Compared compared
                    when compared.relation() instanceof Relation.Affine affine
                    && countIn(affine) instanceof Quantity.HowManyMeet count ->
                    elements.computeIfAbsent(keyOf(count), _ -> new OverTheElements(
                            count.container().inputPosition(),
                            of(count.ofTheElement(), behavior, quantities)));
            case Proposition.Compared compared when askable(compared) ->
                    into.computeIfAbsent(compared.relation(),
                            relation -> OneRelation.of(relation, behavior, quantities));
            // Put to no row: answered as not known where it is asked ({@link #notAsked}).
            case Proposition.Compared _, Proposition.Truth _, Proposition.Present _,
                 Proposition.InCases _, Proposition.SameValue _, Proposition.Unread _,
                 Proposition.OnAnApplication _, Proposition.SomeReachable _ -> { }
            case Proposition.Carried carried -> throw carried.handedToAReader();
        }
    }

    /**
     * Every number of the input {@code stated} reads, the numbers of the elements it reads among
     * them; for a statement {@link #askable} says a row can be asked.
     */
    static Set<NumericTerm> numbersOf(Proposition stated) {
        Set<NumericTerm> out = new LinkedHashSet<>();
        gatherNumbers(stated, out);
        return Collections.unmodifiableSet(out);
    }

    private static void gatherNumbers(Proposition stated, Set<NumericTerm> into) {
        switch (stated) {
            case Proposition.All all -> all.parts().forEach(part -> gatherNumbers(part, into));
            case Proposition.Any any -> any.parts().forEach(part -> gatherNumbers(part, into));
            case Proposition.Some some -> gatherNumbers(some.ofTheElement(), into);
            case Proposition.Compared compared
                    when compared.relation() instanceof Relation.Affine affine
                    && countIn(affine) instanceof Quantity.HowManyMeet count ->
                    gatherNumbers(count.ofTheElement(), into);
            case Proposition.Compared compared -> {
                switch (compared.relation()) {
                    case Relation.Affine affine -> {
                        LinearForm<NumericTerm> form = WhatTheRulesLeave.ofTheInput(affine.form());
                        if (form != null) {
                            into.addAll(form.coefs().keySet());
                        }
                    }
                    case Relation.Ordered(DecisionAtom.OfTheInput(NumericTerm term), Place _,
                                          Rel _) -> into.add(term);
                    case Relation.Ordered _ -> { }
                }
            }
            default -> { }
        }
    }

    /** What some element of a container meeting a statement is read as, whichever way it holds. */
    private static String keyOf(Proposition.Some some) {
        return some.container() + " [" + some.ofTheElement().key() + "]";
    }

    /** What a count of the elements of a container meeting a statement is read as. */
    private static String keyOf(Quantity.HowManyMeet count) {
        return count.container() + " [" + count.ofTheElement().key() + "]";
    }

    /**
     * Every number of a row the statement is read from, the numbers of each element it reads
     * among them.
     */
    List<NumericTerm> numbers() {
        Set<NumericTerm> out = new LinkedHashSet<>();
        relations.values().forEach(each -> out.addAll(each.terms()));
        elements.values().forEach(each -> out.addAll(each.ofTheElement().numbers()));
        return NumericTerms.inOrder(out);
    }

    /**
     * Reads {@code row} the way {@link #at} does and asks nothing of what it read, for the walk
     * that finds which containers a row has to choose an element of.
     *
     * <p>Not the containers a statement reads element by element, nor anything under them: their
     * elements are read together, and a walk that took one for a container to choose in would
     * read the statement under one element where it is about all of them.
     */
    void lookAt(BorderQuantity.Observation row) {
        lookAt(row, Set.of());
    }

    /** The same, beside the containers {@code taken} whose elements are read together. */
    void lookAt(BorderQuantity.Observation row, Set<TermPath> taken) {
        for (OneRelation each : relations.values()) {
            if (each instanceof OneRelation.OnAQuantity read && read.terms().stream()
                    .noneMatch(term -> under(term.subjectPath(), taken))) {
                read.over().lookAt(row);
            }
        }
        for (TermPath each : positions) {
            if (!under(each, taken)) {
                row.at(each);
            }
        }
        for (OverTheElements each : elements.values()) {
            if (!under(each.container(), taken)) {
                row.eachElementOf(each.container());
            }
            Set<TermPath> wider = new HashSet<>(taken);
            wider.add(each.container());
            each.ofTheElement().lookAt(row, wider);
        }
    }

    private static boolean under(TermPath path, Set<TermPath> taken) {
        return taken.stream().anyMatch(path::isAtOrUnder);
    }

    /**
     * Whether the statement holds at {@code row}, read off its own numbers.
     *
     * <p>A relation over a position the row wrote nothing at holds of no value there, so the
     * statement fails there.
     *
     * <p>Each part once at the row, by its spelling: a statement where a line decides holds the
     * same quantifier and the same relation in many places, and each comes to one answer at one
     * row wherever it stands.
     */
    Answer at(BorderQuantity.Observation row) {
        return at(stated, row, new HashMap<>());
    }

    /**
     * How many of the elements of {@code container} the row wrote meet this statement: the least
     * it can be, and how many more it may be where an element could not be read.
     *
     * @return null where the walk could not reach the container
     */
    HowManyAtARow howManyMeetIn(TermPath container, BorderQuantity.Observation row) {
        if (!(row.eachElementOf(container)
                instanceof WalkResult.Reached<List<BorderQuantity.Observation>> reached)) {
            return null;
        }
        List<BorderQuantity.Observation> each = reached.value();
        int meet = 0;
        int unread = 0;
        Set<ReadingGap> why = new LinkedHashSet<>();
        for (BorderQuantity.Observation element : each) {
            switch (at(element)) {
                case Answer.Holds _ -> meet++;
                case Answer.Fails _ -> { }
                case Answer.CouldNotTell(var stopped) -> {
                    unread++;
                    why.addAll(stopped);
                }
            }
        }
        return new HowManyAtARow(meet, unread, why);
    }

    /**
     * How many elements meet a statement at one row.
     *
     * <p>An element the statement could not be read at is neither counted nor left out: the count
     * is somewhere from {@code meet} to {@code meet + unread}, and an element nothing could say of
     * is never one that fails.
     */
    record HowManyAtARow(int meet, int unread, Set<ReadingGap> why) {

        /** The reasons in the order they were met, as {@link Answer.CouldNotTell} keeps them. */
        public HowManyAtARow {
            why = Collections.unmodifiableSet(new LinkedHashSet<>(why));
        }

        /**
         * Whether {@code holds} holds of every count it may be, of none, or of some and not others
         * — which could not be told, and neither can a count {@code holds} could not work out.
         */
        Answer whether(java.util.function.IntFunction<ExactAnswer<Boolean>> holds) {
            boolean some = false;
            boolean every = true;
            Set<ReadingGap> stopped = new LinkedHashSet<>(why);
            for (int count = meet; count <= meet + unread; count++) {
                switch (holds.apply(count)) {
                    case ExactAnswer.Held<Boolean>(Boolean here) -> {
                        some |= here;
                        every &= here;
                    }
                    case ExactAnswer.Unheld<Boolean> unheld -> {
                        stopped.add(ReadingGap.of(unheld.why()));
                        every = false;
                        some = true;
                    }
                }
            }
            if (every) {
                return Answer.HOLDS;
            }
            return !some ? Answer.FAILS : new Answer.CouldNotTell(stopped);
        }
    }

    private Answer at(Proposition part, BorderQuantity.Observation row,
                      Map<String, Answer> answered) {
        Answer known = answered.get(part.key());
        if (known != null) {
            return known;
        }
        Answer answer = atOnce(part, row, answered);
        answered.put(part.key(), answer);
        return answer;
    }

    private Answer atOnce(Proposition part, BorderQuantity.Observation row,
                          Map<String, Answer> answered) {
        return switch (part) {
            case Proposition.Always(boolean holds) -> holds ? Answer.HOLDS : Answer.FAILS;
            // Of the element this row is read with chosen: the last of those holding the value it
            // holds at the position.
            case Proposition.LastToHold(TermPath container, TermPath position, boolean holds,
                                        String _) -> heldAs(holds, switch (
                    row.lastToHold(container, position)) {
                case BorderQuantity.Lastness.Last _ -> Answer.HOLDS;
                case BorderQuantity.Lastness.NotLast _ -> Answer.FAILS;
                case BorderQuantity.Lastness.CouldNotTell(ReadingGap why) ->
                        new Answer.CouldNotTell(Set.of(why));
            });
            case Proposition.Truth(DecisionSubject.AnInput(TermPath at), boolean holds,
                                   String _) -> heldAs(holds, ofItsValue(at, row,
                    value -> value instanceof ObservedValue.Bool(boolean truth) ? truth : null));
            case Proposition.Present(DecisionSubject.AnInput(TermPath at), boolean holds,
                                     String _) -> heldAs(holds, ofItsValue(at, row,
                    value -> !(value instanceof ObservedValue.Absent)));
            case Proposition.InCases(DecisionSubject.AnInput(TermPath at), CasesLeft cases,
                                     boolean holds, String _) when askable(part) ->
                    heldAs(holds, amongCases(at, cases, row));
            case Proposition.SameValue(DecisionSubject.AnInput(TermPath one),
                                       DecisionSubject.AnInput(TermPath other), boolean holds,
                                       String _) -> heldAs(holds, theSame(one, other, row));
            case Proposition.All all -> joined(all.parts().stream()
                    .map(each -> at(each, row, answered)).toList(), true);
            case Proposition.Any any -> joined(any.parts().stream()
                    .map(each -> at(each, row, answered)).toList(), false);
            case Proposition.Some some -> {
                OverTheElements over = elements.get(keyOf(some));
                HowManyAtARow counted = over.ofTheElement().howManyMeetIn(over.container(), row);
                if (counted == null) {
                    yield new Answer.CouldNotTell(Set.of(ReadingGap.COULD_NOT_WALK));
                }
                yield counted.whether(count -> ExactAnswer.held(some.holds() == count > 0));
            }
            case Proposition.Compared compared
                    when compared.relation() instanceof Relation.Affine affine
                    && countIn(affine) instanceof Quantity.HowManyMeet count -> {
                OverTheElements over = elements.get(keyOf(count));
                HowManyAtARow counted = over.ofTheElement().howManyMeetIn(over.container(), row);
                if (counted == null) {
                    yield new Answer.CouldNotTell(Set.of(ReadingGap.COULD_NOT_WALK));
                }
                yield countedAgainst(compared, affine, counted);
            }
            case Proposition.Compared compared when askable(compared) -> {
                Answer held = switch (relations.get(compared.relation())) {
                    case OneRelation.OnAQuantity read -> heldAt(read, row);
                    case OneRelation.NoQuantity unread -> unread.at();
                };
                yield compared.holds() || held instanceof Answer.CouldNotTell ? held
                        : held instanceof Answer.Holds ? Answer.FAILS : Answer.HOLDS;
            }
            case Proposition.Compared _, Proposition.Truth _, Proposition.Present _,
                 Proposition.InCases _, Proposition.SameValue _, Proposition.Unread _,
                 Proposition.OnAnApplication _, Proposition.SomeReachable _ -> notAsked(part);
            case Proposition.Carried carried -> throw carried.handedToAReader();
        };
    }

    /** A count of elements, held against the number {@code compared} holds it against. */
    private static Answer countedAgainst(Proposition.Compared compared, Relation.Affine affine,
                                         HowManyAtARow counted) {
        ExactRatio weight = affine.form().coefs().values().iterator().next();
        Rel rel = compared.holds() ? affine.proposition() : affine.proposition().denied();
        return counted.whether(n -> weight.times(ExactRatio.of(n))
                .flatMap(weighed -> weighed.plus(affine.form().constant()))
                .map(sum -> rel.holds(sum.signum())));
    }

    /**
     * The one container this statement reads nothing beside, or null where it reads anything else
     * or none: what some of its elements meet, how many do, and what the element a reading of a
     * row stands at holds — every one of them about a parameter that is itself the container.
     */
    TermPath containerItIsAbout() {
        Set<TermPath> about = new LinkedHashSet<>();
        for (OverTheElements each : elements.values()) {
            if (each.container().insideAContainer()
                    || !each.ofTheElement().readsOnlyUnder(each.container().element())) {
                return null;
            }
            about.add(each.container());
        }
        List<TermPath> read = new ArrayList<>(positions);
        relations.values().forEach(each ->
                each.terms().forEach(term -> read.add(term.subjectPath())));
        for (TermPath each : read) {
            if (!each.insideAContainer()) {
                return null;
            }
            about.add(each.outermostContainer());
        }
        return about.size() == 1 ? about.iterator().next() : null;
    }

    /** Whether everything this statement reads is at or under {@code root}. */
    private boolean readsOnlyUnder(TermPath root) {
        for (TermPath each : positions) {
            if (!each.isAtOrUnder(root)) {
                return false;
            }
        }
        for (OneRelation each : relations.values()) {
            for (NumericTerm term : each.terms()) {
                if (!term.subjectPath().isAtOrUnder(root)) {
                    return false;
                }
            }
        }
        for (OverTheElements each : elements.values()) {
            if (!each.container().isAtOrUnder(root)
                    || !each.ofTheElement().readsOnlyUnder(root)) {
                return false;
            }
        }
        return true;
    }

    /**
     * What this says of each element of {@code container}, by what it is read as: what some element
     * meets, or what the elements a count counts meet.
     */
    Map<String, AStatementAtARow> ofEachElementOf(TermPath container) {
        Map<String, AStatementAtARow> out = new LinkedHashMap<>();
        elements.forEach((key, over) -> {
            if (over.container().equals(container)) {
                out.put(key, over.ofTheElement());
            }
        });
        return out;
    }

    /**
     * This statement read as what it comes to from how many elements of {@code container} meet
     * each of {@link #ofEachElementOf} — the {@code i}-th of them where {@code index} files it at
     * {@code i} — for containers of up to {@code most} elements.
     *
     * <p>For choosing elements before any row holds them, so it is read once and put to every
     * choice: a part about anything but how many elements meet something is not known, and a part
     * standing in many places is one part.
     */
    Counting counting(TermPath container, Map<String, Integer> index, int most) {
        Counting.Built built = new Counting.Built(most);
        int root = built.node(stated, this, container, index);
        return built.done(root);
    }

    /**
     * A statement as what it comes to from how many elements meet each thing it says of one
     * element: holding, failing, or not known — the last where a part is about anything else, or
     * where the counts leave room for it to come out both ways.
     *
     * <p>Each part once, by its spelling, so a statement holding one quantifier in many places
     * reads it once per choice.
     */
    static final class Counting {

        /** It holds whatever else the elements meet. */
        static final byte HOLDS = 1;
        /** It fails whatever else the elements meet. */
        static final byte FAILS = 0;
        /** It may come out either way. */
        static final byte EITHER = 2;

        /** What a part is, as this reads it. */
        private enum Kind {
            /** Every one of its parts. */
            ALL,
            /** Some one of its parts. */
            ANY,
            /** Some element meeting a thing said of one, or none. */
            SOME,
            /** How many elements meet a thing said of one, held against a number. */
            COUNTED,
            /** Its answer, whatever the elements are. */
            SETTLED
        }

        private final Kind[] kind;
        private final int[][] parts;
        /** The thing said of an element a part counts, for a quantifier or a count. */
        private final int[] counts;
        /** For a quantifier, whether it is some element; for a settled part, its answer. */
        private final byte[] answer;
        /** For a count, what it comes to at each number of elements, {@link #EITHER} where that
         *  number could not be held against it. */
        private final byte[][] byNumber;
        private final int root;

        private Counting(Built built, int root) {
            int size = built.kind.size();
            this.kind = new Kind[size];
            this.parts = new int[size][];
            this.counts = new int[size];
            this.answer = new byte[size];
            this.byNumber = new byte[size][];
            for (int i = 0; i < size; i++) {
                kind[i] = built.kind.get(i);
                parts[i] = built.parts.get(i);
                counts[i] = built.counts.get(i);
                answer[i] = built.answer.get(i);
                byNumber[i] = built.byNumber.get(i);
            }
            this.root = root;
        }

        /**
         * What the statement comes to where {@code meeting} elements meet each thing it says of
         * one element and up to {@code more} besides.
         */
        byte at(int[] meeting, int[] more) {
            byte[] known = new byte[kind.length];
            Arrays.fill(known, (byte) -1);
            return at(root, meeting, more, known);
        }

        private byte at(int node, int[] meeting, int[] more, byte[] known) {
            if (known[node] >= 0) {
                return known[node];
            }
            byte out = switch (kind[node]) {
                case ALL, ANY -> {
                    byte settling = kind[node] == Kind.ALL ? FAILS : HOLDS;
                    byte either = kind[node] == Kind.ALL ? HOLDS : FAILS;
                    for (int part : parts[node]) {
                        byte one = at(part, meeting, more, known);
                        if (one == settling) {
                            either = settling;
                            break;
                        }
                        if (one == EITHER) {
                            either = EITHER;
                        }
                    }
                    yield either;
                }
                case SOME -> {
                    int i = counts[node];
                    boolean held = answer[node] == HOLDS;
                    yield meeting[i] > 0 ? (held ? HOLDS : FAILS)
                            : more[i] == 0 ? (held ? FAILS : HOLDS) : EITHER;
                }
                case COUNTED -> {
                    int i = counts[node];
                    byte[] table = byNumber[node];
                    byte first = EITHER;
                    for (int n = meeting[i]; n <= meeting[i] + more[i]; n++) {
                        byte here = n < table.length ? table[n] : EITHER;
                        if (here == EITHER || (n > meeting[i] && here != first)) {
                            first = EITHER;
                            break;
                        }
                        first = here;
                    }
                    yield first;
                }
                case SETTLED -> answer[node];
            };
            known[node] = out;
            return out;
        }

        /** The parts as they are read, each once. */
        private static final class Built {

            private final int most;
            private final List<Kind> kind = new ArrayList<>();
            private final List<int[]> parts = new ArrayList<>();
            private final List<Integer> counts = new ArrayList<>();
            private final List<Byte> answer = new ArrayList<>();
            private final List<byte[]> byNumber = new ArrayList<>();
            private final Map<String, Integer> read = new HashMap<>();

            Built(int most) {
                this.most = most;
            }

            Counting done(int root) {
                return new Counting(this, root);
            }

            int node(Proposition part, AStatementAtARow of, TermPath container,
                     Map<String, Integer> index) {
                Integer had = read.get(part.key());
                if (had != null) {
                    return had;
                }
                int out = switch (part) {
                    case Proposition.Always(boolean holds) ->
                            add(Kind.SETTLED, null, 0, holds ? HOLDS : FAILS, null);
                    case Proposition.All all -> add(Kind.ALL, all.parts().stream()
                            .mapToInt(each -> node(each, of, container, index)).toArray(), 0,
                            EITHER, null);
                    case Proposition.Any any -> add(Kind.ANY, any.parts().stream()
                            .mapToInt(each -> node(each, of, container, index)).toArray(), 0,
                            EITHER, null);
                    case Proposition.Some some
                            when of.elements.get(keyOf(some)) instanceof OverTheElements over
                            && over.container().equals(container)
                            && index.containsKey(keyOf(some)) ->
                            add(Kind.SOME, null, index.get(keyOf(some)),
                                    some.holds() ? HOLDS : FAILS, null);
                    case Proposition.Compared compared
                            when compared.relation() instanceof Relation.Affine affine
                            && countIn(affine) instanceof Quantity.HowManyMeet count
                            && of.elements.get(keyOf(count)) instanceof OverTheElements over
                            && over.container().equals(container)
                            && index.containsKey(keyOf(count)) ->
                            add(Kind.COUNTED, null, index.get(keyOf(count)), EITHER,
                                    byNumber(compared, affine));
                    default -> add(Kind.SETTLED, null, 0, EITHER, null);
                };
                read.put(part.key(), out);
                return out;
            }

            /** What a count held against a number comes to at each number of elements. */
            private byte[] byNumber(Proposition.Compared compared, Relation.Affine affine) {
                byte[] out = new byte[most + 1];
                for (int n = 0; n <= most; n++) {
                    out[n] = switch (countedAgainst(compared, affine,
                            new HowManyAtARow(n, 0, Set.of()))) {
                        case Answer.Holds _ -> HOLDS;
                        case Answer.Fails _ -> FAILS;
                        case Answer.CouldNotTell _ -> EITHER;
                    };
                }
                return out;
            }

            private int add(Kind what, int[] of, int count, byte said, byte[] table) {
                kind.add(what);
                parts.add(of);
                counts.add(count);
                answer.add(said);
                byNumber.add(table);
                return kind.size() - 1;
            }
        }
    }

    /**
     * What a part no row can be asked about comes to at every row: not known, and why — a part
     * nothing read says what stopped it, and any other is something the row does not write.
     */
    private static Answer notAsked(Proposition part) {
        return new Answer.CouldNotTell(Set.of(ReadingGap.ReachNotRead.of(
                Proposition.firstStopIn(part))));
    }

    private static Answer heldAt(OneRelation.OnAQuantity relation,
                                 BorderQuantity.Observation row) {
        LinearQuantity over = relation.over();
        return switch (over.valuesOf(over.read(row))) {
            case ValuesAtARow.Read(Map<NumericTerm, Place> values) ->
                    switch (relation.holdsAt(values)) {
                        case ExactAnswer.Held<Boolean>(Boolean holds) ->
                                holds ? Answer.HOLDS : Answer.FAILS;
                        case ExactAnswer.Unheld<Boolean> unheld ->
                                new Answer.CouldNotTell(Set.of(ReadingGap.of(unheld.why())));
                    };
            case ValuesAtARow.CouldNotTell(var why) -> new Answer.CouldNotTell(why);
            case ValuesAtARow.NoneHere _ -> Answer.FAILS;
        };
    }

    /**
     * What a row put at {@code at}, asked {@code asked}: holding where it answers true, failing
     * where it answers false or where the row put nothing there, and not read where the walk did
     * not get there or what stands there is no value it answers of.
     */
    private static Answer ofItsValue(TermPath at, BorderQuantity.Observation row,
                                     Function<ObservedValue, Boolean> asked) {
        return switch (row.at(at)) {
            case WalkResult.CouldNotWalk<ObservationAtPoint> _ ->
                    new Answer.CouldNotTell(Set.of(ReadingGap.COULD_NOT_WALK));
            case WalkResult.Reached(ObservationAtPoint standing) -> switch (standing) {
                case ObservationAtPoint.Value(ObservedValue value) -> {
                    Boolean answer = value.unread() != null ? null : asked.apply(value);
                    if (answer == null) {
                        yield new Answer.CouldNotTell(Set.of(ReadingGap.NO_VALUE));
                    }
                    yield answer ? Answer.HOLDS : Answer.FAILS;
                }
                // The row put nothing here under this reading, as a relation over a position a row
                // left empty fails: another reading of the row is where its values here are.
                case ObservationAtPoint.WroteNothing _,
                     ObservationAtPoint.BelongsToAnotherReading _ -> Answer.FAILS;
            };
        };
    }

    /**
     * Whether the value a row put at {@code at} is one of {@code cases}: whether the walk reaches it
     * at the position narrowed to them, as every narrowed position a reading names is reached.
     *
     * <p>Asked of the walk and not of the value. What a row wrote at a position arrives wearing the
     * names the position is declared under, and the walk is what takes them off before it asks
     * which case a value is ({@link Classifier#inside}): the value at a position declared
     * {@code Open = Flag} is in the case it wraps, and a record whose own field is called
     * {@code value} is the case it is. Holding where a value is there and the narrowed walk reaches
     * it, failing where it does not or where the row put nothing there, and not read where the
     * walk did not get there.
     */
    private static Answer amongCases(TermPath at, CasesLeft cases,
                                     BorderQuantity.Observation row) {
        Answer there = ofItsValue(at, row, _ -> true);
        if (!(there instanceof Answer.Holds)) {
            return there;
        }
        // The value this reading holds at the position is there, so nothing of it standing under
        // the cases is that value being another case — whether the row wrote nothing there at
        // all, or only the other elements of a container this reading did not choose did.
        return switch (row.at(DeclaredInput.narrowedTo(at, cases))) {
            case WalkResult.CouldNotWalk<ObservationAtPoint> _ ->
                    new Answer.CouldNotTell(Set.of(ReadingGap.COULD_NOT_WALK));
            case WalkResult.Reached(ObservationAtPoint standing) -> switch (standing) {
                case ObservationAtPoint.Value _ -> Answer.HOLDS;
                case ObservationAtPoint.WroteNothing _,
                     ObservationAtPoint.BelongsToAnotherReading _ -> Answer.FAILS;
            };
        };
    }

    /**
     * Whether a row put one value at both {@code one} and {@code other}: holding where it is the
     * same value, failing where it is two or where the row put nothing at either under this
     * reading, and not read where the walk did not get to one of them or what stands there is no
     * value to compare.
     */
    private static Answer theSame(TermPath one, TermPath other, BorderQuantity.Observation row) {
        if (!(row.at(one) instanceof WalkResult.Reached<ObservationAtPoint>(
                ObservationAtPoint first))
                || !(row.at(other) instanceof WalkResult.Reached<ObservationAtPoint>(
                ObservationAtPoint second))) {
            return new Answer.CouldNotTell(Set.of(ReadingGap.COULD_NOT_WALK));
        }
        if (!(first instanceof ObservationAtPoint.Value(ObservedValue left))
                || !(second instanceof ObservationAtPoint.Value(ObservedValue right))) {
            return Answer.FAILS;
        }
        // A value any part of which could not be read is no value to be equal or unequal to
        // another.
        ReadingGap notRead = ReadingGap.ofAComparisonOf(left);
        if (notRead == null) {
            notRead = ReadingGap.ofAComparisonOf(right);
        }
        if (notRead != null) {
            return new Answer.CouldNotTell(Set.of(notRead));
        }
        return left.equals(right) ? Answer.HOLDS : Answer.FAILS;
    }

    /** {@code answered} where the part is held, and the other way round where it is denied. */
    private static Answer heldAs(boolean holds, Answer answered) {
        return holds || answered instanceof Answer.CouldNotTell ? answered
                : answered instanceof Answer.Holds ? Answer.FAILS : Answer.HOLDS;
    }

    /**
     * Every one of {@code parts} holding where {@code every}, and some one of them where not:
     * settled by one part that settles it whatever the others are, and otherwise not read where a
     * part was not.
     */
    private static Answer joined(List<Answer> parts, boolean every) {
        Answer settling = every ? Answer.FAILS : Answer.HOLDS;
        Set<ReadingGap> unread = new LinkedHashSet<>();
        for (Answer part : parts) {
            if (part.equals(settling)) {
                return settling;
            }
            if (part instanceof Answer.CouldNotTell(Set<ReadingGap> why)) {
                unread.addAll(why);
            }
        }
        if (!unread.isEmpty()) {
            return new Answer.CouldNotTell(unread);
        }
        return every ? Answer.HOLDS : Answer.FAILS;
    }

    /**
     * Where each relation this reads over {@code term} turns over, with every other number it reads
     * standing where {@code beside} says: the value of the term at which the relation's two sides
     * meet.
     *
     * <p>Between two of these, and past the last of them, every relation reads any value of the
     * term the same way. So a value from each run between them and each of them itself are every
     * way a value of the term can answer the relations.
     *
     * <p>Statements about the elements of a container are no relation over the term and turn
     * nowhere here; whether a value meets one is read element by element where it is asked.
     *
     * @return null where a relation over the term reads a number {@code beside} does not hold, or
     *         turns at a number that could not be worked out: where it turns is not known, and a
     *         value chosen from a run could answer it either way
     */
    List<ExactRatio> turnsAt(NumericTerm term, Map<NumericTerm, Place> beside) {
        List<ExactRatio> out = new ArrayList<>();
        for (OneRelation each : relations.values()) {
            switch (each) {
                case OneRelation.OfAForm(LinearQuantity _, LinearForm<NumericTerm> form, Rel _) -> {
                    ExactRatio weight = form.coefs().get(term);
                    if (weight == null) {
                        continue;
                    }
                    ExactAnswer<ExactRatio> rest = ExactAnswer.held(form.constant());
                    for (Map.Entry<NumericTerm, ExactRatio> other : form.coefs().entrySet()) {
                        if (other.getKey().equals(term)) {
                            continue;
                        }
                        Place at = beside.get(other.getKey());
                        if (at == null) {
                            return null;
                        }
                        ExactRatio by = other.getValue();
                        rest = rest.flatMap(sum -> by.times(Count.number(at).exactly())
                                .flatMap(sum::plus));
                    }
                    if (!(rest.flatMap(sum -> sum.negated().dividedBy(weight))
                            instanceof ExactAnswer.Held<ExactRatio>(ExactRatio at))) {
                        return null;
                    }
                    out.add(at);
                }
                case OneRelation.OnAnOrder(LinearQuantity _, NumericTerm on, Place at, Rel _) -> {
                    if (on.equals(term)) {
                        out.add(Count.number(at).exactly());
                    }
                }
                // A relation no row is read at turns wherever it does, which is not known.
                case OneRelation.NoQuantity(LinearForm<NumericTerm> form) -> {
                    if (form.coefs().containsKey(term)) {
                        return null;
                    }
                }
            }
        }
        return out;
    }

    /**
     * Where each relation this reads over {@code term} turns over, for a term whose values are
     * ordered and not counted, with every other position it reads standing where {@code beside}
     * says: the places the term is held against.
     *
     * <p>There is no number to weigh such a term by, so the one place a relation turns is the place
     * the term is compared with: written in the relation, or held at the other position the
     * quantity reads it against ({@link LinearQuantity#levelWith}). Between two of them, and past
     * the last, every relation reads any value of the term the same way.
     *
     * @return null where the quantity a relation reads the term on says no one place is level with
     *         it, which a value chosen from a run could answer either way
     */
    List<Place> placesTurnedAt(NumericTerm term, Map<NumericTerm, Place> beside) {
        List<Place> out = new ArrayList<>();
        for (OneRelation each : relations.values()) {
            switch (each) {
                case OneRelation.OfAForm(LinearQuantity over, LinearForm<NumericTerm> form,
                                         Rel _) -> {
                    if (!form.coefs().containsKey(term)) {
                        continue;
                    }
                    Place level = over.levelWith(term, form.constant(), beside);
                    if (level == null) {
                        return null;
                    }
                    out.add(level);
                }
                case OneRelation.OnAnOrder(LinearQuantity _, NumericTerm on, Place at, Rel _) -> {
                    if (on.equals(term)) {
                        out.add(at);
                    }
                }
                case OneRelation.NoQuantity(LinearForm<NumericTerm> form) -> {
                    if (form.coefs().containsKey(term)) {
                        return null;
                    }
                }
            }
        }
        return out;
    }

    /** A statement about the elements of a container: the container, and what each is asked. */
    private record OverTheElements(TermPath container, AStatementAtARow ofTheElement) {}

    /** One relation, as the quantity a row is read at and what its numbers have to come to. */
    private sealed interface OneRelation {

        /** The numbers of a row the relation is about, whether or not a row can be read at them. */
        List<NumericTerm> terms();

        /** A relation read at a quantity of the row's numbers. */
        sealed interface OnAQuantity extends OneRelation {

            LinearQuantity over();

            /** Whether the relation holds at the numbers a row read at {@link #over}. */
            ExactAnswer<Boolean> holdsAt(Map<NumericTerm, Place> values);

            @Override
            default List<NumericTerm> terms() {
                return over().terms();
            }
        }

        /**
         * A form over positions some of which have no numbers under them, and which is not two of
         * them held against each other: no quantity reads a row at it.
         *
         * <p>Kept, and not dropped from the statement, because what it is about is still the row's:
         * every row answers it as not known, and where a value of one of its terms turns it over is
         * not known either.
         */
        record NoQuantity(LinearForm<NumericTerm> form) implements OneRelation {

            @Override
            public List<NumericTerm> terms() {
                return NumericTerms.inOrder(form.coefs().keySet());
            }

            /** What every row comes to: a sum of what has no number has none to come to. */
            Answer at() {
                return new Answer.CouldNotTell(Set.of(
                        ReadingGap.of(UnheldNumber.NO_REPRESENTATION_EXISTS)));
            }
        }

        /** A form of the input's numbers against nought. */
        record OfAForm(LinearQuantity over, LinearForm<NumericTerm> form, Rel rel)
                implements OnAQuantity {

            @Override
            public ExactAnswer<Boolean> holdsAt(Map<NumericTerm, Place> values) {
                return over.signAt(values, form.constant()).map(rel::holds);
            }
        }

        /** One position against a place on the order it stands on. */
        record OnAnOrder(LinearQuantity over, NumericTerm term, Place at, Rel rel)
                implements OnAQuantity {

            @Override
            public ExactAnswer<Boolean> holdsAt(Map<NumericTerm, Place> values) {
                return ExactAnswer.held(rel.holds(values.get(term).compareTo(at)));
            }
        }

        static OneRelation of(Relation relation, String behavior, Quantities quantities) {
            return switch (relation) {
                case Relation.Affine affine -> {
                    LinearForm<NumericTerm> form = WhatTheRulesLeave.ofTheInput(affine.form());
                    if (form == null) {
                        throw new IllegalStateException("a relation put to rows is over the"
                                + " input's own numbers: " + affine);
                    }
                    LinearQuantity over = Cutting.readAt(behavior, form, quantities);
                    yield over == null ? new NoQuantity(form)
                            : new OfAForm(over, form, affine.proposition());
                }
                case Relation.Ordered(DecisionAtom.OfTheInput(NumericTerm term), Place at, Rel rel)
                        when term.atOnePosition() != null -> new OnAnOrder(
                                Cutting.readAt(behavior, term.atOnePosition(), quantities),
                                term, at, rel);
                case Relation.Ordered ordered -> throw new IllegalStateException("a relation put"
                        + " to rows is over the input's own numbers: " + ordered);
            };
        }
    }

    /**
     * One statement put to rows is another where both state the same and read the same quantities
     * for it: an answer holding one is compared by what it holds.
     */
    @Override
    public boolean equals(Object other) {
        return other instanceof AStatementAtARow that && stated.equals(that.stated)
                && relations.equals(that.relations) && elements.equals(that.elements)
                && positions.equals(that.positions);
    }

    @Override
    public int hashCode() {
        return java.util.Objects.hash(stated, relations, elements, positions);
    }

    /** Every relation over the input's own numbers this reads, for the quantities a reader of it
     *  has to read a row at; a relation no quantity reads a row at has none to read. */
    List<LinearQuantity> over() {
        List<LinearQuantity> out = new ArrayList<>();
        for (OneRelation each : relations.values()) {
            if (each instanceof OneRelation.OnAQuantity read) {
                out.add(read.over());
            }
        }
        return List.copyOf(out);
    }
}
