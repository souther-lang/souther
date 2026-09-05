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
        boolean bySets = mine.stream().anyMatch(PartitionEvidence.BySet.class::isInstance);
        if (!bySets) {
            return new Classed.Composed(onAnOrder.get());
        }
        // A line on the order and a set of the values are two vocabularies, and a class written in
        // one cannot be written in the other: a run of values has a least and a next and a set has
        // neither. So a position reached by both has no single list of classes here.
        if (mine.stream().anyMatch(each -> !(each instanceof PartitionEvidence.BySet))) {
            return new Classed.NotComposed(new BlockReason.ClassesNotComposed());
        }
        // A position whose rules were read as sets and whose cells were not built. The rules are
        // the evidence and the cells are what they come to, and a reader handed the first without
        // the second would have the position divided by nothing it could name.
        if (cells.isEmpty()) {
            return new Classed.NotComposed(new BlockReason.BehaviorDistinctionsTooCostly());
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
        String id = term + "/set/" + bits(cell);
        String label = said(cell);
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
     * Which of the position's rules hold in {@code cell}, as the name a reader never sees.
     *
     * <p>Apart from the label because they answer different questions. What a document calls a class
     * is words, and words are improved; what a run is filed under has to be the same on two compiles
     * of one model and across a wording anybody changes. Made out of the label, every improvement to
     * a sentence would be a class nothing had been recorded at.
     */
    private static String bits(SetDivisions.Cell cell) {
        StringBuilder out = new StringBuilder();
        cell.under().forEach(each -> out.append(each.holds() ? '1' : '0'));
        return out.toString();
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
