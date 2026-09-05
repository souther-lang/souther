package souther.compiler.partition;

import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Text;
import souther.compiler.values.Value;
import souther.compiler.values.ValueSet;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;
import java.util.function.Supplier;

/**
 * What the rules about one position divide it into, in the one vocabulary they can all be said in.
 *
 * <p><b>The question is the vocabulary, and not which kind of evidence arrived.</b> A position is
 * divided by everything the model says about it, and what this decides is whether all of that can be
 * said as one exclusive and exhaustive list of classes. Branching instead on which kind of rule was
 * met, a position reached by two kinds had the classes of whichever kind the branch happened to
 * name, and the other kind's distinctions went missing from the denominator with nothing said.
 *
 * <p><b>Two vocabularies today.</b> A rule can put a line on the order the values are counted on, or
 * tell a set of them from the rest. Both divide a position and neither is the other: a run of values
 * has a least and a next, and a set has neither, so a class in one of them cannot be written in the
 * other. A position reached by both is one this compiler has no single list of classes for, and it
 * comes back saying so rather than divided by the half that happened to be expressible.
 *
 * <p><b>Nothing else is lost by that.</b> Where the classes are not composed, the cuts a line drew
 * and the places the rules part the position are still what they were — they are separate
 * observations about the position and not a projection of the classes. What goes is the denominator,
 * which is the thing that would have been wrong.
 *
 * <p>And a class exists because the model divides the position, never because a value can be written
 * into a row for it. A class nobody can compose a value for says that about itself; dropped instead,
 * the denominator a build is measured against would follow what this compiler can generate.
 */
final class Classing {

    private Classing() {
    }

    /**
     * Which vocabulary a position's rules can all be said in.
     *
     * <p>The one place the question is answered. Asked again by whoever is assembling the measure,
     * the two would agree by having been written alike — until one of them learned about a third
     * vocabulary, and then a position would be divided by one answer and accounted for by the other.
     */
    enum Vocabulary {

        /** Every rule puts a line on the order the values are counted on. */
        ON_AN_ORDER,

        /** Every rule tells a set of the values from the rest. */
        BY_SETS,

        /**
         * The rules are not all in one vocabulary, so the position has no classes.
         *
         * <p>A class on an order and a class that is a set cannot be written as each other: a run
         * of values has a least and a next, and a set has neither. Divided by the half that happened
         * to be expressible, a run would be counted at a class the model tells apart from the one
         * beside it.
         */
        NOT_ONE
    }

    /** Which of the three {@code mine} is, over all of a position's rules and not the first of
     *  them. */
    static Vocabulary vocabularyOf(List<PartitionEvidence> mine) {
        boolean sets = false;
        boolean lines = false;
        for (PartitionEvidence each : mine) {
            if (each instanceof PartitionEvidence.BySet) {
                sets = true;
            } else {
                lines = true;
            }
        }
        if (sets && lines) {
            return Vocabulary.NOT_ONE;
        }
        return sets ? Vocabulary.BY_SETS : Vocabulary.ON_AN_ORDER;
    }

    /** What the rules of one position came to. */
    sealed interface Classed {

        /** Every rule said in one vocabulary, and the classes they leave. */
        record Composed(List<PartitionClass> classes) implements Classed {

            public Composed {
                classes = List.copyOf(classes);
            }
        }

        /**
         * The rules are not all sayable in one vocabulary, so the position has no classes here.
         *
         * <p>Not the classes of the rules that were sayable. A denominator is exclusive and
         * exhaustive or it is not one, and half of a position's rules leave a list that says a run
         * fell in a class the model tells apart from the one beside it.
         */
        record NotComposed(BlockReason.RuleWithoutLineReason why) implements Classed {

            public NotComposed {
                if (why == null) {
                    throw new IllegalArgumentException(
                            "a position whose classes were not composed was stopped by something");
                }
            }
        }
    }

    /**
     * What {@code mine} leaves {@code term} divided into.
     *
     * <p>{@code onAnOrder} is asked for only where the order is the vocabulary — a position divided
     * by sets has no use for it, and working it out would be a reading whose answer is thrown away.
     *
     * @param cells   what the position's set rules leave it divided into, empty where it has none
     * @param writing what a row would carry for a value of this position, or null where nothing
     *                here composes one
     */
    static Classed of(NumericTerm.FromOnePosition term, List<PartitionEvidence> mine,
                      List<SetDivisions.Cell> cells, Supplier<List<PartitionClass>> onAnOrder,
                      Function<Place, FixtureTemplate> writing) {
        switch (vocabularyOf(mine)) {
            case ON_AN_ORDER -> {
                return new Classed.Composed(onAnOrder.get());
            }
            case NOT_ONE -> {
                return new Classed.NotComposed(new BlockReason.ClassesNotComposed());
            }
            default -> { }
        }
        List<PartitionClass> out = new ArrayList<>();
        for (SetDivisions.Cell cell : cells) {
            out.add(classOf(term, cell, writing).ofTheNumber(term));
        }
        return new Classed.Composed(out);
    }

    /** One cell as a class: what it holds, what it is called, and what a row would carry for it. */
    private static PartitionClass classOf(NumericTerm.FromOnePosition term, SetDivisions.Cell cell,
                                          Function<Place, FixtureTemplate> writing) {
        String label = said(cell);
        // The words, and not a name of this method's own. What a document shows a reader is the
        // class identity — every kind of class here is named by what it means, prefixed by the
        // number it is a class of — so a name made out of which rules held would be published in
        // place of the words and a reader would be shown nothing they could act on.
        //
        // Which does tie the identity to the wording: a class renamed is a class nothing was
        // recorded at. That is the arrangement every other class in this measure is already under,
        // and one kind of class keeping its own would be a document that reads two ways.
        String id = term + "/" + label;
        Recognition is = new Recognition.OfASet(cell.values());
        Place stands = someValueIn(cell.values());
        FixtureTemplate written =
                stands == null ? null : writing.apply(stands);
        return written == null
                ? PartitionClass.ungeneratable(id, label, is,
                        "nothing here composed a string of this position that the rules leave in"
                                + " this class")
                : PartitionClass.of(id, label, is,
                        RepresentativeSource.of(written));
    }

    /**
     * What a cell is called: each of the position's rules and how it came out, in the order the
     * body states them.
     *
     * <p>The rules and not where they were written. A class is a set of the position's values, and
     * what names one is what a value in it satisfies — sent to a line and a column, a reader would
     * have to go and read the rule to find out what the class is.
     */
    private static String said(SetDivisions.Cell cell) {
        return cell.under().stream()
                .map(each -> each.holds() ? each.states().saidOf("x") : each.states().deniedOf("x"))
                .reduce((one, other) -> one + " and " + other).orElseThrow();
    }

    /**
     * One string the rules leave in this class, or null where nothing here composes one.
     *
     * <p>A representative and never a condition on the class existing. The model divides the
     * position whether or not this compiler can write a value into a row, and a class dropped for
     * want of one would make the denominator a build is measured against follow what the generator
     * can do.
     */
    private static Place someValueIn(ValueSet values) {
        return switch (values) {
            case ValueSet.Finite it -> it.values().stream()
                    .filter(Value.Text.class::isInstance)
                    .map(each -> (Place) Text.of(((Value.Text) each).value()))
                    .findFirst().orElse(null);
            // What the language holds and a source can carry, which is not the same as what it
            // holds: a class of control characters has a string to offer and none to write, and a
            // row nobody can paste is not a row.
            case ValueSet.Matching it -> {
                String some = it.language().someWritten();
                yield some == null ? null : Text.of(some);
            }
            // Every string but a few, so the shortest one that is not among them. Asked by trying
            // rather than by naming one, because which strings are excluded is the set's answer.
            case ValueSet.Cofinite it -> {
                for (int length = 0; length <= it.excluded().size(); length++) {
                    String tried = "a".repeat(length);
                    if (!it.excluded().contains(new Value.Text(tried))) {
                        yield Text.of(tried);
                    }
                }
                yield null;
            }
        };
    }
}
