package souther.compiler.partition;

import souther.compiler.check.Comparison;
import souther.compiler.check.PathReachability;
import souther.compiler.check.RuleCitation;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleRef;
import souther.compiler.check.StringPredicates;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.ComparisonCatalog;
import souther.compiler.coverage.ComparisonOccurrence;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.diag.Citation;
import souther.compiler.types.BinOp;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;

import java.util.ArrayList;
import java.util.List;

/**
 * One reading of the rules a body writes about its inputs: where each stands, what its names point
 * at, what a row had already satisfied to get there, and what became of it.
 *
 * <p><b>Two answers out of one traversal, and they stay two answers.</b> A comparison places a line
 * on the order a position's values are counted on; a predicate over a string tells a set of those
 * values from the rest. What they have in common is where they stand — which names are in force, what
 * the conditions on the way established, whether what is computed there is read at all — and those
 * are facts about the program point rather than about either kind of rule. So one walk answers them,
 * and what it hands back is a pair of lists and not a sum: a reader wants the comparisons or it wants
 * the predicates, and made to switch over one type it would be reading the fact that both came out of
 * one walk, which is this class's business and nobody else's.
 *
 * <p>Asked once and handed on. Two calls of {@link #of} to take one list each is two traversals of
 * one body, which is the arrangement below is written against.
 *
 * <p><b>Each comparison is read once, here, and what it came to travels with it.</b> A reader that
 * reports why a comparison bears no line reads the answer off the standing and never reads the
 * arithmetic again: read again downstream, the second reading answers about the form when the
 * question was about where the comparison stands, and a form read to the end is described as one
 * nobody could read.
 *
 * <p><b>One walk, because there is one thing being walked.</b> Three facts about a comparison are
 * settled by where it stands in the body, and each was being worked out by a walk of its own: which
 * names are in force, whether what is computed there is read on the way to an answer, and what the
 * evaluation before it established. Two walks threading the same {@code let} rule through the same
 * tree are two chances to disagree about it, and a fact one of them learned to carry is one the
 * other still drops.
 *
 * <p><b>What stands when a comparison runs is a fact about the position, not about a condition.</b>
 * It was read off {@link Condition}, which is a reading of a subtree and so needs a root — and the
 * root anything ever gave it was a fork's condition. So {@code A && B} established nothing for
 * {@code B} while {@code if A then B else false} did, one model spelled two ways with two answers
 * about where a row for a border on {@code B} is looked for; a name standing for {@code A}
 * established nothing either, because a subtree read on its own has no reading of the names above
 * it. A walk of the body has no root to be given and reaches every position, so what a condition is
 * asked is what it can answer: what a subtree coming out one way establishes
 * ({@link ReachingCuts#stating}), and never where the comparisons are.
 *
 * <p>The two operators are where a walk of the body is not a walk of what runs. {@code &&} and
 * {@code ||} settle as soon as they can, so the right operand runs under what the left one coming
 * out its way established — which is the whole of what makes this per comparison rather than per
 * fork. Everything else evaluates its parts under what stood at it.
 */
record BodyReadings(List<ComparisonReading> comparisons,
                    List<StringPredicateReading> stringPredicates) {

    BodyReadings {
        comparisons = List.copyOf(comparisons);
        stringPredicates = List.copyOf(stringPredicates);
    }

    /**
     * One comparison of the body, read where it is written.
     *
     * <p>The reading travels with the comparison because it is not the same at every one of them: a
     * comparison inside an expanded helper is about the argument the call handed it, and read
     * against the names outside the binding it is about nothing at all.
     *
     * @param assumed every condition on the way here, each with what became of it. Empty says
     *                nothing stood on the way, which a comparison at the top of a body is; one this
     *                reading has no arithmetic for is on the list as a decline, so the two are not
     *                one answer
     */
    record ComparisonReading(ComparisonCatalog.Catalogued catalogued, InputReads reads,
                             List<OnTheWay> assumed, BoundaryPolicy.Standing standing) {

        /** Which comparison this is a reading of, which is what every reader joins on. */
        ComparisonOccurrence at() {
            return catalogued.which();
        }

        /** What the recognition established: what the comparison placed, and on which two sides. */
        Comparison comparison() {
            return catalogued.comparison();
        }
    }

    /**
     * One predicate over a string, read where it is applied.
     *
     * <p>What the walk found and no more. Which predicate it is and which strings it states are read
     * off the call by the one table that reads them; where it stands, what its names point at and
     * what a row had satisfied to get there are this walk's, because they are facts about the
     * program point and there is one walk that has them.
     *
     * <p><b>What it admits is not here, and neither is any machine.</b> A set of strings costs
     * something to build, and what a position's rules may build is granted per position and spent as
     * a group — so the sets are worked out where that allowance is, over every predicate that
     * reached one position at once. Held here, each reading would have arrived at its own set one at
     * a time, and which of a position's rules were answered would follow the order this walk
     * happened to meet them in.
     *
     * @param origin  which rule this is a reading of, and which of its readings. One rule the author
     *                wrote is read once per place a helper holding it was expanded, and the readings
     *                divide the position they name differently
     * @param subject the argument the rule is about, for a caller that resolves it to a position
     * @param reads   what the names point at where this stands, which is what resolves the subject
     * @param states  what the one table made of the strings this predicate states there
     * @param assumed every condition on the way here, each with what became of it, as a comparison's
     *                are
     * @param live    whether what is computed here is read on the way to what the behavior answers
     *                with
     */
    record StringPredicateReading(PredicateOrigin origin, Core subject, InputReads reads,
                                  StringPredicates.Reading states, List<OnTheWay> assumed,
                                  boolean live) {

        StringPredicateReading {
            if (origin == null || subject == null || states == null) {
                throw new IllegalArgumentException(
                        "a predicate that was read is some rule, about something, and was read");
            }
            assumed = List.copyOf(assumed);
        }
    }

    /** What each comparison stands under, filed under the site a run through it is recorded at. */
    ReachingCuts reaching(CoverageSites.Plan plan) {
        ReachingCuts.Collected cuts = new ReachingCuts.Collected();
        for (ComparisonReading each : comparisons) {
            // Only where a run through it is written down. What stands on the way to a comparison
            // nothing records is a fact about the body all the same, and there is no run for a
            // reader of this to hold it against.
            if (plan.instruments(each.at())) {
                cuts.reached(each.at(), each.assumed());
            }
        }
        return cuts.made();
    }

    /**
     * What is the same at every comparison of one body: whose body it is, what the plan numbered,
     * the module's names, the reading of the input, what the input's rules leave each quantity, and
     * what the paths leave arriving at each comparison.
     *
     * <p>Where the reading belongs, and it is not in the environment the walk carries. That
     * environment is a function of the program point — a binding met, an arm entered — and the
     * reading is one value for the whole of this walk. Put in it, the reading would be copied at
     * every step and asked of whichever copy a reader happened to hold.
     */
    private record Body(String behavior, CoverageSites.Plan plan,
                        InputReading read,
                        PathReachability.Answers arrives) {

        Symbols symbols() {
            return read.symbols();
        }

        RuleReadingSource rules() {
            return read.rules();
        }
    }

    /** What the walk fills as it goes: the comparisons of the body and the predicates over its
     *  strings, gathered by one traversal because both are facts about where they stand. */
    private record Found(List<ComparisonReading> comparisons,
                         List<StringPredicateReading> stringPredicates) {}

    /**
     * One reading of {@code body}.
     *
     * <p>{@code behavior} is whose body it is, and it is checked rather than trusted. A comparison
     * the catalog named says which behavior's body it stands in, so every one the walk meets is held
     * against what the caller said — a body read under another's name is refused at the first
     * comparison in it. A predicate has no catalog to be named by, which is why the name is a
     * parameter at all: a rule written in a body is one of that behavior's, and two behaviors
     * calling one helper each read its predicate.
     *
     * <p>{@code arrives} is what the walk of the whole body found reaching each comparison, which is
     * one of the two domains a line is held against — the declarations leave the other. It is handed
     * in here because this is where a comparison is read, and a reading of it is made once.
     */
    static BodyReadings of(String behavior, Core body, CoverageSites.Plan plan,
                           InputReading read,
                           InputReads reads,
                           PathReachability.Answers arrives) {
        if (behavior == null) {
            throw new IllegalArgumentException("a body is somebody's body");
        }
        Found found = new Found(new ArrayList<>(), new ArrayList<>());
        walk(body, new Body(behavior, plan, read, arrives), reads,
                LiveFlow.of(body), List.of(), true, found);
        return new BodyReadings(found.comparisons(), found.stringPredicates());
    }

    /**
     * @param assumed what evaluating everything before this position established
     * @param live    whether what is computed here is read on the way to what the behavior answers
     *                with. Carried down because everything inside a value nothing reads is read by
     *                nothing either
     */
    private static void walk(Core e, Body in, InputReads reads, LiveFlow flow,
                             List<OnTheWay> assumed, boolean live, Found out) {
        CoverageSites.Plan plan = in.plan();
        Symbols symbols = in.symbols();
        RuleReadingSource ruleSource = in.rules();
        ComparisonCatalog.Catalogued catalogued = e instanceof Core.Binary binary
                ? plan.comparisons().at(binary).orElse(null) : null;
        if (catalogued != null) {
            // What the caller said this body is, held against what the catalog says. A name handed
            // in is a name a caller chose, and the one thing here that already knows whose body it
            // is refuses a walk reading one behavior's body under another's name.
            if (!in.behavior().equals(catalogued.which().behavior())) {
                throw new IllegalArgumentException("this is " + catalogued.which().behavior()
                        + "'s body and it is being read as " + in.behavior() + "'s");
            }
            // What the catalog holds, kept whole. It carries which comparison this is, what the
            // recognition established and where it is written, and all three travel to whoever
            // reads this — taken apart here, a reader wanting one of them again would have to find
            // its way back to the node, which is the arrangement this replaces.
            Comparison comparison = catalogued.comparison();
            // Read only where the policy admits it, and under the names in force here, which is
            // the one environment the comparison is about. `answer` is null: a body has nothing
            // that is the answer.
            //
            // And under what arrives at it, which is where a body's comparison differs from a
            // clause's: it stands somewhere, and what the conditions on the way leave is the other
            // domain its line is held against. Required and not looked up leniently — the policy
            // refuses a comparison the plan numbers no site for, so reaching here is the site
            // existing. Asked as an optional, a policy that stopped proving it would hand the
            // reading below the answer that restricts nothing, and this stage disagreeing with the
            // plan would go out as an arrival nobody could project.
            BoundaryPolicy.Standing standing =
                    BoundaryPolicy.refuses(catalogued.which(), plan, live)
                    .<BoundaryPolicy.Standing>map(BoundaryPolicy.Standing.Refused::new)
                    .orElseGet(() -> new BoundaryPolicy.Standing.Admitted(
                            ComparisonAssessment.of(catalogued.which().behavior(), comparison,
                                    catalogued.at(), in.read(), reads,
                                    null, false,
                                    in.arrives().arrivalAt(catalogued.which()))));
            out.comparisons().add(
                    new ComparisonReading(catalogued, reads, assumed, standing));
        }
        // And a predicate over a string, which is the other kind of rule a body writes about a
        // position. Read here and not by a walk of its own: which names are in force, what a row
        // had satisfied to get here and whether what is computed here is read at all are facts
        // about the program point, and a second traversal is a second chance to disagree about
        // them. What it means is asked of the one table that reads such a call, with the text
        // reached through the names this walk has ({@link InputReads#writtenStringOf}) — so a rule
        // written under `let prefix = "JP"` states what a rule written with the string states.
        StringPredicates.Stated stated = e instanceof Core.PreservedCall call
                ? StringPredicates.statedBy(call, symbols,
                        written -> reads.writtenStringOf(written, symbols))
                : null;
        if (stated != null && e instanceof Core.PreservedCall call && call.origin().isWritten()) {
            // Its own number, taken here, and what it names is the reading rather than the rule.
            // Which rule it is came from the source; how many times that rule is read is a fact
            // about this body, and this walk is what knows it.
            out.stringPredicates().add(new StringPredicateReading(
                    new PredicateOrigin(
                            new RuleRef.Predicate(in.behavior(), call.origin()),
                            new PredicateOccurrence(out.stringPredicates().size()),
                            new RuleCitation.WrittenAt(
                                    Citation.of(call.pos()))),
                    stated.subject(), reads, stated.reading(), assumed, live));
        }
        switch (e) {
            // The right operand runs only where the left came out the way that leaves the answer
            // unsettled, so what it stands under is what that says. Asked of the operand and not of
            // any fork above it: there need not be one, and where there is, this is what the fork
            // would have been reading anyway.
            case Core.Binary both when both.op() == BinOp.AND -> {
                walk(both.left(), in, reads, flow, assumed, live, out);
                walk(both.right(), in, reads, flow,
                        taking(both.left(), true, in.read().domain(), reads, assumed, ruleSource), live, out);
            }
            case Core.Binary either when either.op() == BinOp.OR -> {
                walk(either.left(), in, reads, flow, assumed, live, out);
                walk(either.right(), in, reads, flow,
                        taking(either.left(), false, in.read().domain(), reads, assumed, ruleSource),
                        live, out);
            }
            // The condition under what stood above the fork, and each arm under what that arm proves
            // of it. A comparison inside a condition is not below the fork: it runs to decide it.
            case Core.If iff -> {
                walk(iff.cond(), in, reads, flow, assumed, live, out);
                walk(iff.then(), in, reads, flow,
                        taking(iff.cond(), true, in.read().domain(), reads, assumed, ruleSource), live, out);
                walk(iff.els(), in, reads, flow,
                        taking(iff.cond(), false, in.read().domain(), reads, assumed, ruleSource), live, out);
            }
            // What a `let` computes is read on the way to the answer only where the name is read;
            // everywhere else a value stands in a body it is consumed by what it stands in. And its
            // body is where the name stands for what was bound to it.
            case Core.LetIn let -> {
                walk(let.value(), in, reads, flow, assumed, live && flow.reads(let), out);
                walk(let.body(), in, reads.and(let.binder(), let.value()), flow, assumed, live,
                        out);
            }
            // And each arm under what the arm says the value it matched turned out to be. A name
            // the arm binds is the scrutinee's position narrowed to that case, so a comparison
            // written inside an arm draws its line on a position the reading of the input has —
            // read without it, every rule an author writes inside a `match` was about nothing.
            //
            // The same narrowing is what a row has to be for the arm to be reached at all, so it
            // goes onto the account beside the conditions a guard states. Walked without it, a line
            // inside an arm was owed a row by a walk that had been told nothing stood on the way to
            // it, and the row composed for it was written in whichever arm the values fell in.
            case Core.Match match -> {
                walk(match.scrutinee(), in, reads, flow, assumed, live, out);
                for (Core.Case arm : match.cases()) {
                    walk(arm.body(), in, reads.insideArm(match, arm, symbols), flow,
                            entering(match, arm, in.read().domain(), reads, assumed, ruleSource), live, out);
                }
            }
            default -> Core.forEachChild(e, child ->
                    walk(child, in, reads, flow, assumed, live, out));
        }
    }

    /**
     * What stands past {@code node} coming out {@code holding}: what stood before it, and what that
     * says.
     *
     * <p>Asked of {@link ReachingCuts#stating}, which is the same rule that says what reaching an
     * arm of a fork establishes. Both are "this subtree came out this way, so what follows", and
     * written apart they would agree by having been derived alike — until one of them learned to
     * read a shape of condition the other did not.
     */
    private static List<OnTheWay> taking(Core node, boolean holding,
                                         souther.compiler.inputs.InputDomain inputs,
                                         InputReads reads, List<OnTheWay> assumed,
                                         RuleReadingSource ruleSource) {
        List<OnTheWay> out = new ArrayList<>(assumed);
        out.addAll(ReachingCuts.stating(Condition.of(node, reads, ruleSource.symbols()), inputs,
                holding, ruleSource));
        return List.copyOf(out);
    }

    /** The same, for what standing inside one arm of a fork establishes ({@link
     *  ReachingCuts#entering}). */
    private static List<OnTheWay> entering(Core.Match match, Core.Case arm,
                                           souther.compiler.inputs.InputDomain inputs,
                                           InputReads reads, List<OnTheWay> assumed,
                                           RuleReadingSource ruleSource) {
        List<OnTheWay> out = new ArrayList<>(assumed);
        out.add(ReachingCuts.entering(match, arm, inputs, reads, ruleSource));
        return List.copyOf(out);
    }
}
