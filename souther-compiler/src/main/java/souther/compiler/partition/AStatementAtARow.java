package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Rel;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * A statement over a row's own numbers, put to rows: each relation it is over, read as the quantity
 * a row is read at.
 *
 * <p>Read the way a line over the same quantity reads a row ({@link LinearQuantity#valuesOf}), so
 * what a row holds at a position is one answer whether a line, the place it decides, or a count of
 * the elements meeting the statement asks for it.
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

    private AStatementAtARow(Proposition stated, Map<Relation, OneRelation> relations) {
        this.stated = stated;
        // In the order the relations were met, which is the order their containers are found in
        // when a row is walked for them.
        this.relations = Collections.unmodifiableMap(new LinkedHashMap<>(relations));
    }

    /**
     * Whether a row's own numbers say whether {@code stated} holds at it: relations over the
     * input's own numbers, joined, or nothing asked at all.
     *
     * <p>Anything else is no statement a row can be asked about. A truth, a quantifier or something
     * nobody read is not settled by the numbers a row writes, and a reader that took the statement
     * without it would count rows it says nothing about.
     */
    static boolean askable(Proposition stated) {
        return switch (stated) {
            case Proposition.Always _ -> true;
            case Proposition.All all -> all.parts().stream().allMatch(AStatementAtARow::askable);
            case Proposition.Any any -> any.parts().stream().allMatch(AStatementAtARow::askable);
            case Proposition.Compared compared -> switch (compared.relation()) {
                case Relation.Affine affine -> WhatTheRulesLeave.ofTheInput(affine.form()) != null;
                case Relation.Ordered(DecisionAtom.OfTheInput(NumericTerm term), Place _, Rel _) ->
                        term.atOnePosition() != null;
                case Relation.Ordered _ -> false;
            };
            default -> false;
        };
    }

    /**
     * {@code stated}, ready to be asked of rows.
     *
     * @param quantities the reading of the input, which says which order each number is on
     * @throws IllegalStateException where {@code stated} is not {@link #askable}
     */
    static AStatementAtARow of(Proposition stated, String behavior, Quantities quantities) {
        Map<Relation, OneRelation> relations = new LinkedHashMap<>();
        gather(stated, behavior, quantities, relations);
        return new AStatementAtARow(stated, relations);
    }

    private static void gather(Proposition stated, String behavior, Quantities quantities,
                               Map<Relation, OneRelation> into) {
        switch (stated) {
            case Proposition.Always _ -> { }
            case Proposition.All all ->
                    all.parts().forEach(part -> gather(part, behavior, quantities, into));
            case Proposition.Any any ->
                    any.parts().forEach(part -> gather(part, behavior, quantities, into));
            case Proposition.Compared compared -> into.computeIfAbsent(compared.relation(),
                    relation -> OneRelation.of(relation, behavior, quantities));
            default -> throw new IllegalStateException("a statement put to rows is over relations"
                    + " of the input's own numbers, and this is " + stated);
        }
    }

    /** Every quantity a row is read at to say whether the statement holds there. */
    List<LinearQuantity> over() {
        return relations.values().stream().map(OneRelation::over).toList();
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

    private Answer at(Proposition part, BorderQuantity.Observation row) {
        return switch (part) {
            case Proposition.Always(boolean holds) -> holds ? Answer.HOLDS : Answer.FAILS;
            case Proposition.All all -> joined(all.parts().stream()
                    .map(each -> at(each, row)).toList(), true);
            case Proposition.Any any -> joined(any.parts().stream()
                    .map(each -> at(each, row)).toList(), false);
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
}
