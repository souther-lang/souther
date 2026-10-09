package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.NumericTerms;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

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

            public CouldNotTell {
                why = Set.copyOf(why);
            }
        }

        Answer HOLDS = new Holds();

        Answer FAILS = new Fails();
    }

    private final Proposition stated;
    private final Map<Relation, OneRelation> relations;
    private final Map<String, OverTheElements> elements;

    private AStatementAtARow(Proposition stated, Map<Relation, OneRelation> relations,
                             Map<String, OverTheElements> elements) {
        this.stated = stated;
        // In the order the relations were met, which is the order their containers are found in
        // when a row is walked for them.
        this.relations = Collections.unmodifiableMap(new LinkedHashMap<>(relations));
        this.elements = Collections.unmodifiableMap(new LinkedHashMap<>(elements));
    }

    /**
     * Whether a row's own numbers say whether {@code stated} holds at it: relations over the
     * input's own numbers, joined, statements about the elements of a container the input holds —
     * some element meeting something, or how many do, against a number — or nothing asked at all.
     *
     * <p>Anything else is no statement a row can be asked about. A truth, something nobody read, or
     * a count against another of the input's numbers is not settled by the numbers a row writes
     * the way a relation is, and a reader that took the statement without it would count rows it
     * says nothing about.
     */
    static boolean askable(Proposition stated) {
        return switch (stated) {
            case Proposition.Always _ -> true;
            case Proposition.All all -> all.parts().stream().allMatch(AStatementAtARow::askable);
            case Proposition.Any any -> any.parts().stream().allMatch(AStatementAtARow::askable);
            case Proposition.Some some -> askable(some.ofTheElement());
            case Proposition.Compared compared -> switch (compared.relation()) {
                case Relation.Affine affine -> WhatTheRulesLeave.ofTheInput(affine.form()) != null
                        || countIn(affine) instanceof Quantity.HowManyMeet count
                                && askable(count.ofTheElement());
                case Relation.Ordered(DecisionAtom.OfTheInput(NumericTerm term), Place _, Rel _) ->
                        term.atOnePosition() != null;
                case Relation.Ordered _ -> false;
            };
            default -> false;
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
     * @param quantities the reading of the input, which says which order each number is on
     * @throws IllegalStateException where {@code stated} is not {@link #askable}
     */
    static AStatementAtARow of(Proposition stated, String behavior, Quantities quantities) {
        Map<Relation, OneRelation> relations = new LinkedHashMap<>();
        Map<String, OverTheElements> elements = new LinkedHashMap<>();
        gather(stated, behavior, quantities, relations, elements);
        return new AStatementAtARow(stated, relations, elements);
    }

    private static void gather(Proposition stated, String behavior, Quantities quantities,
                               Map<Relation, OneRelation> into,
                               Map<String, OverTheElements> elements) {
        switch (stated) {
            case Proposition.Always _ -> { }
            case Proposition.All all -> all.parts()
                    .forEach(part -> gather(part, behavior, quantities, into, elements));
            case Proposition.Any any -> any.parts()
                    .forEach(part -> gather(part, behavior, quantities, into, elements));
            case Proposition.Some some -> elements.computeIfAbsent(keyOf(some),
                    _ -> new OverTheElements(some.container(),
                            of(some.ofTheElement(), behavior, quantities)));
            case Proposition.Compared compared
                    when compared.relation() instanceof Relation.Affine affine
                    && countIn(affine) instanceof Quantity.HowManyMeet count ->
                    elements.computeIfAbsent(keyOf(count), _ -> new OverTheElements(
                            count.container(), of(count.ofTheElement(), behavior, quantities)));
            case Proposition.Compared compared -> into.computeIfAbsent(compared.relation(),
                    relation -> OneRelation.of(relation, behavior, quantities));
            default -> throw new IllegalStateException("a statement put to rows is over relations"
                    + " of the input's own numbers, and this is " + stated);
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
        relations.values().forEach(each -> out.addAll(each.over().terms()));
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
            if (each.over().terms().stream().noneMatch(term -> under(term.subjectPath(), taken))) {
                each.over().lookAt(row);
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
     */
    Answer at(BorderQuantity.Observation row) {
        return at(stated, row);
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

        public HowManyAtARow {
            why = Set.copyOf(why);
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

    private Answer at(Proposition part, BorderQuantity.Observation row) {
        return switch (part) {
            case Proposition.Always(boolean holds) -> holds ? Answer.HOLDS : Answer.FAILS;
            case Proposition.All all -> joined(all.parts().stream()
                    .map(each -> at(each, row)).toList(), true);
            case Proposition.Any any -> joined(any.parts().stream()
                    .map(each -> at(each, row)).toList(), false);
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
                ExactRatio weight = affine.form().coefs().values().iterator().next();
                Rel rel = compared.holds() ? affine.proposition()
                        : affine.proposition().denied();
                yield counted.whether(n -> weight.times(ExactRatio.of(n))
                        .flatMap(weighed -> weighed.plus(affine.form().constant()))
                        .map(sum -> rel.holds(sum.signum())));
            }
            case Proposition.Compared compared -> {
                Answer held = heldAt(relations.get(compared.relation()), row);
                yield compared.holds() || held instanceof Answer.CouldNotTell ? held
                        : held instanceof Answer.Holds ? Answer.FAILS : Answer.HOLDS;
            }
            default -> throw new IllegalStateException("a statement put to rows is over relations"
                    + " of the input's own numbers, and this is " + part);
        };
    }

    private static Answer heldAt(OneRelation relation, BorderQuantity.Observation row) {
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
            }
        }
        return out;
    }

    /** A statement about the elements of a container: the container, and what each is asked. */
    private record OverTheElements(TermPath container, AStatementAtARow ofTheElement) {}

    /** One relation, as the quantity a row is read at and what its numbers have to come to. */
    private sealed interface OneRelation {

        LinearQuantity over();

        /** Whether the relation holds at the numbers a row read at {@link #over}. */
        ExactAnswer<Boolean> holdsAt(Map<NumericTerm, Place> values);

        /** A form of the input's numbers against nought. */
        record OfAForm(LinearQuantity over, LinearForm<NumericTerm> form, Rel rel)
                implements OneRelation {

            @Override
            public ExactAnswer<Boolean> holdsAt(Map<NumericTerm, Place> values) {
                return OrderedAffineBoundary.along(form.coefs(), values)
                        .flatMap(sum -> sum.plus(form.constant()))
                        .map(sum -> rel.holds(sum.signum()));
            }
        }

        /** One position against a place on the order it stands on. */
        record OnAnOrder(LinearQuantity over, NumericTerm term, Place at, Rel rel)
                implements OneRelation {

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
                    yield new OfAForm(Cutting.readAt(behavior, form, quantities), form,
                            affine.proposition());
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
                && relations.equals(that.relations) && elements.equals(that.elements);
    }

    @Override
    public int hashCode() {
        return java.util.Objects.hash(stated, relations, elements);
    }

    /** Every relation over the input's own numbers this reads, for the quantities a reader of it
     *  has to read a row at. */
    List<LinearQuantity> over() {
        List<LinearQuantity> out = new ArrayList<>();
        relations.values().forEach(each -> out.add(each.over()));
        return List.copyOf(out);
    }
}
