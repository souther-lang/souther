package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.check.PredicateStatement;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Text;
import souther.compiler.values.Allowance;
import souther.compiler.values.Sameness;
import souther.compiler.values.Value;
import souther.compiler.values.ValueSet;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.function.Function;

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

    /**
     * Which of the three {@code mine} is, over all of a position's rules and not the first of them.
     *
     * <p>Asked of what each distinction can be said as, and never of which reader produced it. A
     * value singled out of a string is a set of one value and is also a place on the order the
     * strings are counted on, so it goes whichever way the rules beside it go; a value singled out
     * of a number is only the second. A line is only the second, and a set told from the rest is
     * only the first.
     *
     * <p>A position every rule of which draws a line keeps the vocabulary it has always had. Asked
     * the other way round, a position singling out one string would change which algebra its
     * classes are written in the day a set rule was written beside it, and the classes it already
     * had would be rewritten under a rule that says nothing about them.
     */
    static Vocabulary vocabularyOf(List<PartitionEvidence> mine, Carrier carrier) {
        boolean sets = true;
        boolean lines = true;
        for (PartitionEvidence each : mine) {
            sets &= asASet(each, carrier) != null;
            lines &= !(each instanceof PartitionEvidence.BySet);
        }
        if (lines) {
            return Vocabulary.ON_AN_ORDER;
        }
        return sets ? Vocabulary.BY_SETS : Vocabulary.NOT_ONE;
    }

    /**
     * What one piece of evidence tells apart, said as sets, or null where it cannot be said so.
     *
     * <p>The capability the vocabulary is chosen by. A rule that tells a set from the rest has both
     * sides already; a value singled out of a string is the one value and every other string, which
     * is the same distinction written in this algebra rather than a second answer about it. A line
     * has no such writing, and neither has a value singled out of anything but a string — a run of
     * values is not a set this compiler holds, and saying so is what keeps the two apart.
     */
    private static AsASet asASet(PartitionEvidence evidence, Carrier carrier) {
        return switch (evidence) {
            case PartitionEvidence.BySet(SetDivision it) ->
                    new AsASet(it.whenTrue(), it.whenFalse(), it.statement());
            case PartitionEvidence.Singles(GuardThresholds.Guards.Singled it) -> {
                if (!(carrier instanceof Carrier.Text) || !(it.value() instanceof Text text)) {
                    yield null;
                }
                Value one = new Value.Text(text.at());
                yield new AsASet(new ValueSet.Finite(Set.of(one)),
                        new ValueSet.Cofinite(Set.of(one)),
                        new PredicateStatement.Equalling(text.at()));
            }
            case PartitionEvidence.Divides _ -> null;
        };
    }

    /**
     * One distinction of a position, said as the values on either side of it.
     *
     * <p>What a piece of evidence comes to once it is asked to speak this vocabulary. Every kind of
     * evidence that can be said this way answers with one of these and the rest answer with
     * nothing, which is what makes the question about the distinction rather than about which
     * reader produced it.
     */
    private record AsASet(ValueSet whenTrue, ValueSet whenFalse, PredicateStatement states) {}

    /** What the rules of one position came to. */
    sealed interface Classed {

        /**
         * The order the values are counted on is the vocabulary, so the classes are the runs of
         * them the caller works out.
         *
         * <p>Its own answer and not an empty list of classes. What this says is which algebra the
         * position's classes are written in, and a position genuinely divided into none is a
         * different thing — read off the emptiness, the two would be one answer and a position
         * whose rules divide it nowhere would be sent to the reading that builds runs.
         */
        record OnTheOrder() implements Classed {}

        /** Every rule said as sets, and the classes they leave. */
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
     * What {@code mine} leaves {@code term} divided into, given everything that reached it.
     *
     * @param blocked the rules that would have divided this position and did not. One of them and
     *                there are no classes, whatever the rest are written in
     * @param writing what a row would carry for a value of this position, or null where nothing
     *                here composes one
     */
    static Classed of(NumericTerm.FromOnePosition term, List<PartitionEvidence> mine,
                      List<ClassingBlocker> blocked, Carrier carrier, ValueSet admits,
                      Allowance<NumericTerm.FromOnePosition> allowance,
                      Function<Place, FixtureTemplate> writing) {
        // Asked before the vocabulary, and kept as it was said. A rule missing from the denominator
        // is missing however the rules beside it are written, and what stopped it is a fact about
        // that rule rather than about what the position's rules come to together.
        if (!blocked.isEmpty()) {
            return new Classed.NotComposed(blocked.get(0).why());
        }
        switch (vocabularyOf(mine, carrier)) {
            case ON_AN_ORDER -> {
                return new Classed.OnTheOrder();
            }
            case NOT_ONE -> {
                return new Classed.NotComposed(new BlockReason.ClassesNotComposed());
            }
            default -> { }
        }
        List<AsASet> said = new ArrayList<>();
        mine.forEach(each -> said.add(asASet(each, carrier)));
        List<Cell> cells = refined(term, admits, said, allowance);
        if (cells == null) {
            return new Classed.NotComposed(new BlockReason.BehaviorDistinctionsTooCostly());
        }
        // A rule the position leaves nothing on one side of divides nothing here, however the
        // strings fall. An invariant restricts and a behavior divides what is left, so the two
        // sides of a rule can both hold strings and one of them hold no value this position may
        // take — and a class published for it is one no run is ever counted at.
        if (cells.size() < 2) {
            return new Classed.NotComposed(new BlockReason.PredicateTellingNothingApart());
        }
        List<PartitionClass> out = new ArrayList<>();
        for (Cell cell : cells) {
            out.add(classOf(term, cell, writing).ofTheNumber(term));
        }
        return new Classed.Composed(out);
    }

    /**
     * One class the rules about a position leave it divided into.
     *
     * <p>A cell of the coarsest partition every distinction's two sides are a union of cells of,
     * which is what several rules about one position come to. Two rules leave four, and a run of the
     * model is in exactly one of them — so four is what the rows are owed at, and the two rules
     * taken one at a time would ask for a distinction the other one already made.
     *
     * <p><b>What each rule states and how it came out, in the order they were read.</b> Where a run
     * falls is decided by each of them coming out one way or the other, and that is what tells a
     * cell from its neighbours — so the assignment is what a cell is, and a reader names the class
     * out of it.
     */
    record Cell(ValueSet values, List<Answered> under) {

        Cell {
            if (values == null || values.isEmpty()) {
                throw new IllegalArgumentException(
                        "a class of a position holds a value; an empty one is no class of it");
            }
            under = List.copyOf(under);
        }

        /** The same cell, with one more rule coming out {@code holding} and what that leaves. */
        Cell and(ValueSet narrowed, PredicateStatement states, boolean holding) {
            List<Answered> wider = new ArrayList<>(under);
            wider.add(new Answered(states, holding));
            return new Cell(narrowed, wider);
        }
    }

    /** One of a position's rules, and whether a value in the cell satisfies it. */
    record Answered(PredicateStatement states, boolean holds) {

        Answered {
            if (states == null) {
                throw new IllegalArgumentException("a rule that came out one way states something");
            }
        }
    }

    /**
     * What {@code said} leaves {@code term} divided into, or null where the allowance ran out.
     *
     * <p>Each distinction in turn against what the ones before it left: a cell either satisfies it
     * or does not, and one that would hold no value is no class of the position and is dropped
     * rather than published as a class no run is ever counted at.
     *
     * <p>Null and not the cells so far. A partition is exclusive and exhaustive or it is not one,
     * and cells the meets got through before the allowance ran out are neither — read as the
     * position's classes, the values in the ones nobody finished would be owed no row at all.
     */
    private static List<Cell> refined(NumericTerm.FromOnePosition term, ValueSet admits,
                                      List<AsASet> said,
                                      Allowance<NumericTerm.FromOnePosition> allowance) {
        // What the position holds, which is what the rules of a body divide. Started from the
        // strings instead, a rule would divide values the declarations already refused and the
        // position would come back with classes no run is ever in.
        List<Cell> cells = new ArrayList<>();
        cells.add(new Cell(admits, List.of()));
        for (AsASet each : said) {
            List<Cell> narrower = new ArrayList<>();
            for (Cell cell : cells) {
                for (boolean holding : new boolean[] {true, false}) {
                    ValueSet side = holding ? each.whenTrue() : each.whenFalse();
                    Allowance.Composed met =
                            allowance.meet(Sameness.Block.of(term), cell.values(), side);
                    if (met.gaveUp()) {
                        return null;
                    }
                    if (!met.set().isEmpty()) {
                        narrower.add(cell.and(met.set(), each.states(), holding));
                    }
                }
            }
            cells = narrower;
        }
        return cells;
    }

    /** One cell as a class: what it holds, what it is called, and what a row would carry for it. */
    private static PartitionClass classOf(NumericTerm.FromOnePosition term, Cell cell,
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
    private static String said(Cell cell) {
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
