package souther.compiler.partition;

import souther.compiler.check.PredicateStatement;
import souther.compiler.check.Symbols;
import souther.compiler.check.StringPredicates;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.PathResolution;
import souther.compiler.regex.PatternPlan;
import souther.compiler.values.AdmittedPlan;
import souther.compiler.values.Allowance;
import souther.compiler.values.Realizations;
import souther.compiler.values.Sameness;
import souther.compiler.values.ValueSet;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What a behavior's rules about the strings at its positions divide those positions into.
 *
 * <p>The one crossing from a plan to a set on this side. What a reading of a body hands on is the
 * rule and the strings it names; what a partition works with is the values on either side of it, and
 * turning the first into the second is making a machine. Done anywhere a reader felt like it, the
 * machine would be built under whatever allowance that reader happened to hold, and the same rule
 * would divide the position differently depending on who asked.
 *
 * <p><b>The position is the unit, and it is all of them or none of them.</b> Two rules about one
 * position are two distinctions of one denominator, and a reader hearing about one of them is
 * hearing about a partition the model does not draw. So every plan of a position — both sides of
 * every one of its rules — goes to the allowance as one group, and a position whose group cannot be
 * built divides by nothing rather than by the rules that happened to be cheap
 * ({@link Allowance#realizeAll}).
 *
 * <p><b>Both sides are asked for, and neither is derived from the other.</b> The values a rule does
 * not admit are a plan like the values it does ({@link PatternPlan#notMatching}), so they are built
 * where everything else is and are charged for there. Left to a caller, the complement would be the
 * one expensive operation done outside the arrangement that exists to bound it.
 *
 * <p><b>On its own allowance, and not the one a declaration's answer draws on.</b> What a behavior
 * tells apart is not a projection of what a position admits: a position whose own answer stopped
 * short still has its body's rules read here, and raising what a declaration may build must not make
 * a class appear ({@link AdequacyPolicy.OfTheMeasures#allowanceForBehaviorDistinctions}).
 *
 * <p>And every rule handed in is answered for. One that divides comes back as a division and one
 * that does not comes back as what became of it, so nothing that reached here leaves without a
 * sentence about it.
 */
final class SetDivisions {

    private SetDivisions() {
    }

    /**
     * What the rules came to.
     *
     * @param divided   the positions divided, as evidence a partition reads like any other
     * @param undivided the rules that divided nothing, each with what became of it
     * @param cells     what the divisions of each position leave it divided into, which is the
     *                  coarsest partition every one of them is a union of cells of
     */
    record Read(List<PartitionEvidence> divided, List<Undivided> undivided,
                Map<NumericTerm.FromOnePosition, List<Cell>> cells) {

        Read {
            divided = List.copyOf(divided);
            undivided = List.copyOf(undivided);
            cells = Map.copyOf(cells);
        }
    }

    /**
     * One class the rules about a position leave it divided into.
     *
     * <p>A cell of the coarsest partition every rule's two sides are a union of cells of, which is
     * what several rules about one position come to. {@code startsWith("JP", code)} and
     * {@code endsWith("X", code)} leave four, and a run of the model is in exactly one of them —
     * so four is what the rows are owed at, and the two rules taken one at a time would ask for a
     * distinction the other one already made.
     *
     * <p><b>What each rule states and how it came out, in the order the body states them.</b> Where
     * a run falls is decided by each of the position's rules coming out one way or the other, and
     * that is what tells a cell from its neighbours — so the assignment is what a cell is, and a
     * reader names the class out of it. Held as two sets of rules, the order a document lists them
     * in would come from a set rather than from the model.
     *
     * <p>And it is the statements, not the origins. Two copies of one helper state one rule at two
     * positions, and the class each leaves is called the same thing; which reading produced the
     * evidence is what the evidence carries and is no part of what a class is.
     *
     * @param values the values in it, which no other cell of the position holds
     * @param under  each of the position's rules and how it came out here, in the order the body
     *               states them
     */
    record Cell(ValueSet values, List<Answered> under) {

        Cell {
            if (values == null || values.isEmpty()) {
                throw new IllegalArgumentException(
                        "a class of a position holds a value; an empty one is no class of it");
            }
            under = List.copyOf(under);
            if (under.isEmpty()) {
                throw new IllegalArgumentException(
                        "a cell is what the rules of a position left, so some rule made it");
            }
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
     * One rule that reached here and divided no position.
     *
     * <p>The rule and not the position. A rule whose subject no position answers has no position to
     * file this under, and one whose group was refused is answered for at the position all the same
     * — so what a reader is given is which rule it was, and where the reason is about a position it
     * is the reason that says so.
     */
    record Undivided(PredicateOrigin by, BlockReason why) {

        Undivided {
            if (by == null || why == null) {
                throw new IllegalArgumentException(
                        "a rule that divided nothing is some rule, and something became of it");
            }
        }
    }

    /**
     * The purse {@code term}'s machines are bought from, which is the position on its own.
     *
     * <p>An allowance is per block of positions the model holds one value across, because two
     * positions an equality ties together have one set to build and one purse to build it from. A
     * rule about the strings at a position ties it to nothing — what it states is true of the values
     * standing here and says no word about any other position — so each term is its own block, and
     * two positions that happen to be written with the same predicate pay for their machines apart.
     *
     * <p>Said here once, so that a reader is not left working out from two call sites whether the
     * grouping this stage does is the same grouping the allowance does. It is not: the group here
     * is every rule about one position, and the block is every position that holds one value.
     */
    private static Sameness.Block<NumericTerm.FromOnePosition> purseOf(
            NumericTerm.FromOnePosition term) {
        return Sameness.Block.of(term);
    }

    /** One rule read as far as the plans for its two sides, waiting on its position's group. */
    private record Asked(PredicateOrigin by, PredicateStatement states,
                         NumericTerm.FromOnePosition term,
                         AdmittedPlan whenTrue, AdmittedPlan whenFalse) {}

    /**
     * What {@code read} divides, built under {@code allowance}.
     *
     * <p>{@code symbols} and the reading each rule carries are what turn its subject into a
     * position: a rule inside an expanded helper is about the argument the call handed it, so where
     * it stands is asked of the reading that stands there and never of the body as a whole.
     */
    static Read of(PredicateReadings read, Symbols symbols,
                   Allowance<NumericTerm.FromOnePosition> allowance) {
        List<Asked> asked = new ArrayList<>();
        List<Undivided> undivided = new ArrayList<>();
        for (PredicateReadings.Reading each : read.predicates()) {
            ask(each, symbols, asked, undivided);
        }
        // Every plan of a position, gathered before anything is built. A set written into two rules
        // is one plan and is charged once, which is what taking them as a group comes to.
        Map<NumericTerm.FromOnePosition, Set<AdmittedPlan>> byTerm = new LinkedHashMap<>();
        for (Asked each : asked) {
            Set<AdmittedPlan> plans =
                    byTerm.computeIfAbsent(each.term(), _ -> new LinkedHashSet<>());
            plans.add(each.whenTrue());
            plans.add(each.whenFalse());
        }
        Map<NumericTerm.FromOnePosition, Realizations> answers = new LinkedHashMap<>();
        byTerm.forEach((term, plans) ->
                answers.put(term, allowance.realizeAll(purseOf(term), plans)));
        List<PartitionEvidence> divided = new ArrayList<>();
        for (Asked each : asked) {
            divide(each, answers.get(each.term()), divided, undivided);
        }
        // And what the divisions of each position leave it divided into, worked out here because
        // this is where the allowance is. Two rules about one position are not two partitions of
        // it: a run falls in one cell of what they come to between them, and the cells are met out
        // of their sides — which is machine work, and machine work outside an allowance is a
        // measure deciding for itself how long it may take.
        Map<NumericTerm.FromOnePosition, List<Cell>> cells = new LinkedHashMap<>();
        for (NumericTerm.FromOnePosition term : byTerm.keySet()) {
            List<SetDivision> here = divided.stream()
                    .filter(each -> each.at().equals(term))
                    .map(each -> ((PartitionEvidence.BySet) each).division()).toList();
            if (here.isEmpty()) {
                continue;
            }
            List<Cell> made = refined(term, here, allowance);
            // The position's group again, and for the reason it was a group in the first place.
            // Cells nobody could finish are a partition of the position this compiler does not
            // have, and publishing the divisions beside it would leave a reader holding rules
            // whose classes are not the ones the position is measured at.
            if (made == null) {
                divided.removeIf(each -> each.at().equals(term));
                here.forEach(each -> undivided.add(new Undivided(each.origin(),
                        new BlockReason.BehaviorDistinctionsTooCostly())));
                continue;
            }
            cells.put(term, made);
        }
        return new Read(divided, undivided, cells);
    }

    /**
     * What {@code divisions} leave {@code term} divided into, or null where the allowance ran out.
     *
     * <p>Each rule in turn against what the rules before it left: a cell either satisfies it or
     * does not, and one that would hold no value is no class of the position and is dropped rather
     * than published as a class no run is ever counted at.
     *
     * <p>Null and not the cells so far. A partition is exclusive and exhaustive or it is not one,
     * and cells the meets got through before the allowance ran out are neither — read as the
     * position's classes, the values in the ones nobody finished would be owed no row at all.
     */
    private static List<Cell> refined(NumericTerm.FromOnePosition term, List<SetDivision> divisions,
                                      Allowance<NumericTerm.FromOnePosition> allowance) {
        SetDivision first = divisions.get(0);
        List<Cell> cells = new ArrayList<>();
        cells.add(new Cell(first.whenTrue(), List.of(new Answered(first.statement(), true))));
        cells.add(new Cell(first.whenFalse(), List.of(new Answered(first.statement(), false))));
        for (SetDivision each : divisions.subList(1, divisions.size())) {
            List<Cell> narrower = new ArrayList<>();
            for (Cell cell : cells) {
                for (boolean holding : new boolean[] {true, false}) {
                    ValueSet side = holding ? each.whenTrue() : each.whenFalse();
                    Allowance.Composed met =
                            allowance.meet(purseOf(term), cell.values(), side);
                    if (met.gaveUp()) {
                        return null;
                    }
                    if (!met.set().isEmpty()) {
                        narrower.add(cell.and(met.set(), each.statement(), holding));
                    }
                }
            }
            cells = narrower;
        }
        return cells;
    }

    /**
     * One rule as the plans for its two sides, or as what became of it.
     *
     * <p>Exhaustive with no {@code default}: an outcome the table of predicates learns is one
     * somebody decides about here rather than one that quietly takes its neighbour's answer.
     */
    private static void ask(PredicateReadings.Reading each, Symbols symbols,
                            List<Asked> asked, List<Undivided> undivided) {
        // Where the rule's subject stands, read where the rule stands. A subject no single position
        // answers is a rule about a value made from the position rather than about the position, and
        // there is no denominator for it to divide.
        if (!(each.reads().pathOf(each.subject(), symbols) instanceof PathResolution.At at)) {
            undivided.add(new Undivided(each.origin(),
                    new BlockReason.RuleAboutADerivedValue()));
            return;
        }
        NumericTerm.FromOnePosition term = new NumericTerm.ValueOf(at.path());
        switch (each.reading()) {
            case StringPredicates.Reading.Accepting it -> asked.add(new Asked(each.origin(),
                    each.statement(), term,
                    new AdmittedPlan.Pattern(PatternPlan.of(it.accepts())),
                    new AdmittedPlan.Pattern(PatternPlan.notMatching(it.accepts()))));
            case StringPredicates.Reading.PatternNotRead it -> undivided.add(new Undivided(
                    each.origin(), BlockReason.forAPatternNotRead(it.why())));
            // A rule whose text this compiler did not work out is a rule it did not read. Said as
            // anything about the values, it would be a distinction reported as absent from the model
            // when what is absent is this compiler's reading of it.
            case StringPredicates.Reading.WrittenArgumentNotKnown _ -> undivided.add(
                    new Undivided(each.origin(), new BlockReason.UnreadValueRule()));
        }
    }

    /** One rule as the division it came to, out of what its position's group was built to. */
    private static void divide(Asked each, Realizations answer,
                               List<PartitionEvidence> divided, List<Undivided> undivided) {
        if (!(answer instanceof Realizations.Exact built)) {
            undivided.add(new Undivided(each.by(),
                    new BlockReason.BehaviorDistinctionsTooCostly()));
            return;
        }
        ValueSet whenTrue = built.of(each.whenTrue());
        ValueSet whenFalse = built.of(each.whenFalse());
        // A rule with nothing on one of its sides puts every value of the model on the other, which
        // is the position undivided. Published, it would put a class in the denominator that no run
        // is ever counted at and every row would be owed one for it.
        if (whenTrue.isEmpty() || whenFalse.isEmpty()) {
            undivided.add(new Undivided(each.by(),
                    new BlockReason.PredicateTellingNothingApart()));
            return;
        }
        divided.add(new PartitionEvidence.BySet(new SetDivision(
                each.term(), whenTrue, whenFalse, each.states(), each.by())));
    }
}
