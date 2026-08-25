package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.coverage.Observation;
import souther.compiler.inputs.InputDomain;
import souther.compiler.reading.Interaction;
import souther.compiler.reading.CoverageRead;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;
import souther.compiler.query.Shapes;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What a combination comes to when the search for a row at it ran out of room.
 *
 * <p>A combination is looked for at each of the things it can be asking, and each of those is walked
 * outward from where the reading leaves the positions it says nothing about. What a walk may cost is
 * counted in runs, because reaching the arm is what a row has to do and only the behavior can say
 * whether it did.
 *
 * <p>So a bound leaves the search incomplete only where it was reached in front of a run that
 * nobody did. A candidate the model refuses never reached the behavior; a candidate whose values
 * something was already watched at has its answer already. Counted per candidate instead, a
 * combination whose remaining candidates were all values a run had been seen at came back saying
 * the search had stopped — a claim about the model made on the strength of a limit.
 *
 * <p>The combinations here are of one model, searched in one run, against runs that all missed
 * alike. What differs between them is how many positions each is about, which is how many the
 * search was left to choose, and so how many of its candidates are values nothing has run yet.
 */
class ASearchThatStoppedSaysSoRatherThanNamingItsLastRefusalTest {

    /** Two decisions and a position free of both, which is eight rows in all. */
    private static final String ONE_FREE = shipping("rush: Bool");

    /** The same with a second position free of both, which is more values than a reading may run
     *  for. */
    private static final String TWO_FREE = shipping("rush: Bool, gift: Bool");

    private static String shipping(String free) {
        return """
                module example.shipping

                data Membership = Premium | Standard

                data Delivery = Express | Regular

                data Fee = Int
                    invariant value >= 0

                behavior shippingFee : (member: Membership, delivery: Delivery, %1$s) -> Fee
                    constructs Fee

                let baseFee (tier: Membership): Int =
                    match tier with
                        | Premium -> 0
                        | Standard -> 500

                let expressFee (speed: Delivery): Int =
                    match speed with
                        | Express -> 500
                        | Regular -> 0

                let shippingFee (member, delivery, %2$s) =
                    Fee(baseFee(member) + expressFee(delivery))
                """.formatted(free, free.replaceAll(": Bool", ""));
    }

    /**
     * A combination the bound stopped in front of an unrun candidate says the search stopped.
     *
     * <p>Two positions left to choose is four values, and a reading may be run for three. The fourth
     * is a set of values nothing has been watched at: what the three that were run came to is those
     * candidates' news, and offered as the combination's answer it stands for a space this search
     * never entered.
     */
    @Test
    void aCombinationLeftWithAnUnrunCandidateSaysTheSearchStopped() {
        Generator.GenerationResult filled = fill(Model.of(TWO_FREE, "shippingFee"), _ -> MISSED);

        assertEquals(Generator.UnresolvedCombination.Reason.SEARCH_LIMIT,
                reasonFor(filled, List.of("member=Premium", "delivery=Express")),
                "a fourth set of values, and no run left to watch it at: " + filled.unresolved());
    }

    /**
     * A combination whose candidates were all tried says the candidates were not witnesses.
     *
     * <p>Which is something about the model, and it may be said because nothing was left untried
     * behind it.
     */
    @Test
    void aCombinationEveryCandidateMissedSaysTheCandidatesWereNotWitnesses() {
        Generator.GenerationResult filled = fill(Model.of(ONE_FREE, "shippingFee"), _ -> MISSED);

        assertEquals(Generator.UnresolvedCombination.Reason.NO_CERTIFIED_WITNESS,
                reasonFor(filled, List.of("member=Premium", "delivery=Express")),
                "one position left to choose, and both of its values were run: "
                        + filled.unresolved());
    }

    /**
     * A run already watched at some values costs nothing, so a search that ends on them is complete.
     *
     * <p>{@code member=Premium} leaves two positions to choose, which is four sets of values — more
     * than the three a reading may be run for. By the time this combination is looked in, every one
     * of them is a set something has already been watched at, so the reading spends nothing and
     * reaches the end of its candidates.
     *
     * <p>Counted per candidate, the fourth of them stopped the search and the combination answered
     * that this run had given up. What it has is four candidates and an answer for each.
     */
    @Test
    void candidatesWhoseValuesAlreadyRanDoNotStopTheSearch() {
        Generator.GenerationResult filled = fill(Model.of(ONE_FREE, "shippingFee"), _ -> MISSED);

        assertEquals(Generator.UnresolvedCombination.Reason.NO_CERTIFIED_WITNESS,
                reasonFor(filled, List.of("member=Premium")),
                "more candidates than a reading may run for, and every one of them already run: "
                        + filled.unresolved());
    }

    /**
     * One run per set of values, however many combinations were looked for at them.
     *
     * <p>Eight is every row this behavior has: two memberships, two deliveries, and the position
     * free of both. Every combination of the body is looked in and none of them is a witness, so the
     * search reaches all eight — and reaches each of them once.
     */
    @Test
    void aSetOfValuesIsRunOnceHoweverManyCombinationsWantIt() {
        int[] runs = {0};

        fill(Model.of(ONE_FREE, "shippingFee"), _ -> {
            runs[0]++;
            return MISSED;
        });

        assertEquals(8, runs[0], "one run per set of values this behavior has");
    }

    /** A run that did nothing at all, which is a run that missed every combination. */
    private static final Generator.Watched MISSED =
            new Generator.Watched.Ran(Observation.NONE);

    /** What the search made of the one combination named by {@code classes}. */
    private static Generator.UnresolvedCombination.Reason reasonFor(
            Generator.GenerationResult filled, List<String> classes) {
        return filled.unresolved().stream()
                .filter(each -> each.classes().equals(classes))
                .findFirst()
                .orElseThrow(() -> new AssertionError(
                        "the combination " + classes + " is one this run looked for a row at: "
                                + filled.unresolved()))
                .reason();
    }

    private static Generator.GenerationResult fill(Model model, Generator.Trial trial) {
        return Generator.fill(model.subject(), List.of(), Generator.CandidateCheck.ANY,
                model.read(), trial, Budgets.generation());
    }

    private record Model(Generator.Subject subject, CoverageRead.Read read) {

        /** The groups of the one reading, for a caller asking about the combinations alone. */
        List<Interaction> groups() {
            return read.interactions();
        }

        static Model of(String source, String behavior) {
            Compilation compilation = Compilation.ofSource(source, "Main");
            compilation.answerEverything();
            String module = compilation.modules().get(0);
            Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
            Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
            Symbols symbols = Scopes.derived(compilation.db(), module).value();
            Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
            assertNotNull(prepared);
            assertNotNull(sigs);
            assertNotNull(checked);
            Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                    .filter(b -> b.name().equals(behavior)).findFirst().orElseThrow();
            Sig sig = sigs.get(behavior);
            InputDomain inputs =
                    compilation.db().ask(new Adequacy.Inputs(module)).value().get(behavior);
            assertNotNull(inputs, "the behavior's inputs were read");
            Core body = checked.behaviorBodies().get(behavior);
            assertNotNull(body, "the behavior under test has a body");
            return new Model(new Generator.Subject(
                    new BehaviorInputs(spec.params().stream().map(Hir.Param::name).toList(),
                            sig.inputTypes(), symbols,
                            souther.compiler.query.ReadAs.THE_COMPILATION_DOES),
                    Partitions.of(spec.name(), inputs, symbols,
                            souther.compiler.query.ReadAs.THE_COMPILATION_DOES).axes(), HeldCounts.of(inputs, symbols)),
                    CoverageRead.of(spec.name(), body,
                            CoverageSites.of(checked.behaviorBodies(), checked.decisions(),
                checked.supplied()), inputs,
                            symbols));
        }
    }
}
