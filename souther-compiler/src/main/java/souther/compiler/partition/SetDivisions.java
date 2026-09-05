package souther.compiler.partition;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.PredicateStatement;
import souther.compiler.check.Symbols;
import souther.compiler.check.StringPredicates;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.PathResolution;
import souther.compiler.regex.PatternPlan;
import souther.compiler.values.AdmittedPlan;
import souther.compiler.values.Allowance;
import souther.compiler.values.Realizations;
import souther.compiler.values.Sameness;
import souther.compiler.values.ValueSet;
import souther.compiler.types.BindingId;

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
 * <p><b>One rule at a time, and what a position comes to is not asked here.</b> What several rules
 * leave a position between them is a question about every rule that reached it, and the rules of a
 * behavior's body are not all of them — a value singled out by a comparison divides the same
 * position. Answered here, the denominator would be completed by the reader that can see least of
 * it, out of the rules it happened to read.
 *
 * <p><b>The position is still the unit of what is built.</b> Both sides of every rule of a position
 * go to the allowance as one group, so which of them a reader hears about does not follow the order
 * they were walked in ({@link Allowance#realizeAll}).
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
public final class SetDivisions {

    private SetDivisions() {
    }

    /** What a behavior with no body to read comes to, which is no rules and nothing became of
     *  them. Not the same as a body that states none: there the walk ran and found nothing, and
     *  here there was nothing to walk. */
    public static final Read NONE = new Read(List.of(), List.of());

    /**
     * What the rules came to.
     *
     * @param divided the positions divided, as evidence a partition reads like any other
     * @param blocked the rules that would have divided a position and did not, which is what keeps
     *                its classes from being composed out of the ones that worked
     */
    public record Read(List<PartitionEvidence> divided, List<ClassingBlocker> blocked) {

        public Read {
            divided = List.copyOf(divided);
            blocked = List.copyOf(blocked);
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
    public static Read of(String behavior, AnalysisBody body, InputReading read,
                          Map<BindingId, String> parameters, ElementBindings elements,
                          Allowance<NumericTerm.FromOnePosition> allowance) {
        return of(PredicateReadings.of(behavior, body, read, parameters, elements),
                read.symbols(), allowance);
    }

    /**
     * The same, of a reading already made.
     *
     * <p>Not the way in from outside. Which tree a body's rules are read off is settled here, and a
     * caller given the choice could hand over a reading of the tree a backend emits — where every
     * one of these rules has been expanded into what it does, so the behavior would come back
     * stating nothing about the strings at any of its positions.
     */
    static Read of(PredicateReadings read, Symbols symbols,
                   Allowance<NumericTerm.FromOnePosition> allowance) {
        List<Asked> asked = new ArrayList<>();
        List<ClassingBlocker> blocked = new ArrayList<>();
        for (PredicateReadings.Reading each : read.predicates()) {
            ask(each, symbols, asked, blocked);
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
            divide(each, answers.get(each.term()), divided, blocked);
        }
        return new Read(divided, blocked);
    }

    /**
     * One rule as the plans for its two sides, or as what became of it.
     *
     * <p>Exhaustive with no {@code default}: an outcome the table of predicates learns is one
     * somebody decides about here rather than one that quietly takes its neighbour's answer.
     */
    private static void ask(PredicateReadings.Reading each, Symbols symbols,
                            List<Asked> asked, List<ClassingBlocker> blocked) {
        // Where the rule's subject stands, read where the rule stands. A subject no single position
        // answers is a rule about a value made from the position rather than about the position, and
        // there is no denominator for it to divide.
        if (!(each.reads().pathOf(each.subject(), symbols) instanceof PathResolution.At at)) {
            // Where the value it is about came from, which is not where it stands: a rule about
            // what an operation made from a position divides no position, and the one the value
            // came from is where a reader looks for what became of the rule.
            if (each.reads().cameFrom(each.subject(), symbols)
                    instanceof PathResolution.At(var from)) {
                blocked.add(new ClassingBlocker(new NumericTerm.ValueOf(from), each.origin(),
                        new BlockReason.RuleAboutADerivedValue()));
            }
            return;
        }
        NumericTerm.FromOnePosition term = new NumericTerm.ValueOf(at.path());
        switch (each.reading()) {
            case StringPredicates.Reading.Accepting it -> asked.add(new Asked(each.origin(),
                    each.statement(), term,
                    new AdmittedPlan.Pattern(PatternPlan.of(it.accepts())),
                    new AdmittedPlan.Pattern(PatternPlan.notMatching(it.accepts()))));
            case StringPredicates.Reading.PatternNotRead it -> blocked.add(new ClassingBlocker(
                    term, each.origin(), BlockReason.forAPatternNotRead(it.why())));
            // A rule whose text this compiler did not work out is a rule it did not read. Said as
            // anything about the values, it would be a distinction reported as absent from the model
            // when what is absent is this compiler's reading of it.
            case StringPredicates.Reading.WrittenArgumentNotKnown _ -> blocked.add(
                    new ClassingBlocker(term, each.origin(),
                            new BlockReason.UnreadValueRule()));
        }
    }

    /** One rule as the division it came to, out of what its position's group was built to. */
    private static void divide(Asked each, Realizations answer,
                               List<PartitionEvidence> divided, List<ClassingBlocker> blocked) {
        if (!(answer instanceof Realizations.Exact built)) {
            blocked.add(new ClassingBlocker(each.term(), each.by(),
                    new BlockReason.BehaviorDistinctionsTooCostly()));
            return;
        }
        ValueSet whenTrue = built.of(each.whenTrue());
        ValueSet whenFalse = built.of(each.whenFalse());
        // A rule with nothing on one of its sides puts every value of the model on the other, which
        // is the position undivided. Published, it would put a class in the denominator that no run
        // is ever counted at and every row would be owed one for it.
        if (whenTrue.isEmpty() || whenFalse.isEmpty()) {
            blocked.add(new ClassingBlocker(each.term(), each.by(),
                    new BlockReason.PredicateTellingNothingApart()));
            return;
        }
        divided.add(new PartitionEvidence.BySet(new SetDivision(
                each.term(), whenTrue, whenFalse, each.states(), each.by())));
    }
}
