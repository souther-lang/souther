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
import java.util.Objects;
import java.util.Set;

/**
 * One of the lines a statement of several relations draws, read in one case of where the statement
 * turns on it.
 *
 * <p>The two together because the second is part of what the line is. {@code Int.max(a, b) <= g}
 * turns on {@code a = g} only where {@code b <= g}, so a row at that line with {@code b} above
 * {@code g} is answered the same way on both sides of it: it stands at the line and says nothing
 * about it. A reader holding the line without where it decides would take that row for one that
 * met it.
 *
 * <p>One case and not all of them. Where a line decides may be one of several things, and each is
 * somewhere a row can be composed to be; the line is read once in each, and a row meets it in any.
 *
 * @param part    which of the statement's lines this is
 * @param decides the case: parts of the statement that hold together beside the line, where
 *                crossing it turns the statement round. Over the relations the statement holds,
 *                every one of them a relation over the input's own numbers — so a row's values say
 *                whether it holds
 */
public record WhereAPartDecides(PartOfAComparison part, Proposition decides) {

    public WhereAPartDecides {
        Objects.requireNonNull(part, "a line of a statement is one of its lines");
        Objects.requireNonNull(decides, "a line decides somewhere, or nowhere");
    }

    /** Whether a row is somewhere the line decides, or what kept that from being read. */
    sealed interface AtARow {

        /** The row is somewhere the statement turns on the line. */
        record Decides() implements AtARow {}

        /** The row is somewhere the statement does not turn on the line, or holds no value one of
         *  the relations is over. */
        record DecidesNothing() implements AtARow {}

        /** A number the relations are over could not be read at the row, for these reasons. */
        record CouldNotTell(Set<ReadingGap> why) implements AtARow {

            public CouldNotTell {
                why = Set.copyOf(why);
            }
        }

        AtARow DECIDES = new Decides();

        AtARow DECIDES_NOTHING = new DecidesNothing();
    }

    /**
     * This, put to rows: each relation it is over, as the quantity a row is read at.
     *
     * <p>Read the way a line over the same quantity reads a row ({@link BorderQuantity#valuesOf}),
     * so what a row holds at a position is one answer whether a line or the place it decides asks
     * for it.
     *
     * @param quantities the reading of the input, which says which order each number is on
     */
    AskedOfRows askedOfRows(String behavior, Quantities quantities) {
        Map<Relation, OneRelation> relations = new LinkedHashMap<>();
        gather(decides, behavior, quantities, relations);
        return new AskedOfRows(decides, relations);
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
            default -> throw new IllegalStateException("where a line of a statement decides is"
                    + " over relations of the input's own numbers, and this is " + stated);
        }
    }

    /** One relation, as the quantity a row is read at and what its numbers have to come to. */
    private sealed interface OneRelation {

        BorderQuantity over();

        /** Whether the relation holds at the numbers a row read at {@link #over}. */
        ExactAnswer<Boolean> holdsAt(Map<NumericTerm, Place> values);

        /** A form of the input's numbers against nought. */
        record OfAForm(BorderQuantity over, LinearForm<NumericTerm> form, Rel rel)
                implements OneRelation {

            @Override
            public ExactAnswer<Boolean> holdsAt(Map<NumericTerm, Place> values) {
                return OrderedAffineBoundary.along(form.coefs(), values)
                        .flatMap(sum -> sum.plus(form.constant()))
                        .map(sum -> rel.holds(sum.signum()));
            }
        }

        /** One position against a place on the order it stands on. */
        record OnAnOrder(BorderQuantity over, NumericTerm term, Place at, Rel rel)
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
                        throw new IllegalStateException("a relation a line decides under is over"
                                + " the input's own numbers: " + affine);
                    }
                    yield new OfAForm(Cutting.readAt(behavior, form, quantities), form,
                            affine.proposition());
                }
                case Relation.Ordered(DecisionAtom.OfTheInput(NumericTerm term), Place at, Rel rel)
                        when term.atOnePosition() != null -> new OnAnOrder(
                                Cutting.readAt(behavior, term.atOnePosition(), quantities),
                                term, at, rel);
                case Relation.Ordered ordered -> throw new IllegalStateException("a relation a"
                        + " line decides under is over the input's own numbers: " + ordered);
            };
        }
    }

    /** Where a line decides, ready to be asked of rows. */
    static final class AskedOfRows {

        private final Proposition decides;
        private final Map<Relation, OneRelation> relations;

        private AskedOfRows(Proposition decides, Map<Relation, OneRelation> relations) {
            this.decides = decides;
            // In the order the relations were met, which is the order their containers are found
            // in when a row is walked for them.
            this.relations = Collections.unmodifiableMap(new LinkedHashMap<>(relations));
        }

        /** Every quantity a row is read at to say whether it is somewhere the line decides. */
        List<BorderQuantity> over() {
            return relations.values().stream().map(OneRelation::over).toList();
        }

        /**
         * Whether {@code row} is somewhere the line decides, read off its own numbers.
         *
         * <p>A relation over a position the row wrote nothing at holds of no value there, so the
         * row is not somewhere it holds.
         */
        AtARow at(BorderQuantity.Observation row) {
            return at(decides, row);
        }

        private AtARow at(Proposition stated, BorderQuantity.Observation row) {
            return switch (stated) {
                case Proposition.Always(boolean holds) ->
                        holds ? AtARow.DECIDES : AtARow.DECIDES_NOTHING;
                case Proposition.All all -> joined(all.parts().stream()
                        .map(part -> at(part, row)).toList(), true);
                case Proposition.Any any -> joined(any.parts().stream()
                        .map(part -> at(part, row)).toList(), false);
                case Proposition.Compared compared -> {
                    AtARow held = heldAt(relations.get(compared.relation()), row);
                    yield compared.holds() || held instanceof AtARow.CouldNotTell ? held
                            : held instanceof AtARow.Decides ? AtARow.DECIDES_NOTHING
                            : AtARow.DECIDES;
                }
                default -> throw new IllegalStateException("where a line of a statement decides"
                        + " is over relations of the input's own numbers, and this is " + stated);
            };
        }

        private static AtARow heldAt(OneRelation relation, BorderQuantity.Observation row) {
            BorderQuantity over = relation.over();
            return switch (over.valuesOf(over.read(row))) {
                case ValuesAtARow.Read(Map<NumericTerm, Place> values) ->
                        switch (relation.holdsAt(values)) {
                            case ExactAnswer.Held<Boolean>(Boolean holds) ->
                                    holds ? AtARow.DECIDES : AtARow.DECIDES_NOTHING;
                            case ExactAnswer.Unheld<Boolean> unheld ->
                                    new AtARow.CouldNotTell(Set.of(ReadingGap.of(unheld.why())));
                        };
                case ValuesAtARow.CouldNotTell(var why) -> new AtARow.CouldNotTell(why);
                case ValuesAtARow.NoneHere _ -> AtARow.DECIDES_NOTHING;
            };
        }

        /**
         * Every one of {@code parts} holding where {@code every}, and some one of them where not:
         * settled by one part that settles it whatever the others are, and otherwise not read
         * where a part was not.
         */
        private static AtARow joined(List<AtARow> parts, boolean every) {
            AtARow settling = every ? AtARow.DECIDES_NOTHING : AtARow.DECIDES;
            Set<ReadingGap> unread = new LinkedHashSet<>();
            for (AtARow part : parts) {
                if (part.equals(settling)) {
                    return settling;
                }
                if (part instanceof AtARow.CouldNotTell(Set<ReadingGap> why)) {
                    unread.addAll(why);
                }
            }
            if (!unread.isEmpty()) {
                return new AtARow.CouldNotTell(unread);
            }
            return every ? AtARow.DECIDES : AtARow.DECIDES_NOTHING;
        }
    }
}
