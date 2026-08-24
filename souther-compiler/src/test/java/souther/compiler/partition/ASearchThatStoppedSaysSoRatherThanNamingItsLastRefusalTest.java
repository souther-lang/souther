package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.ComparisonOutcome;
import souther.compiler.coverage.ControlClaim;
import souther.compiler.coverage.ControlPointId;
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

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a combination comes to when the search for a row at it ran out of room.
 *
 * <p>A combination is looked for at each of the things it can be asking, and each of those is walked
 * outward from where the reading leaves the positions it says nothing about. Both walks are bounded,
 * and a bound is a fact about the search: past it are candidates nothing tried, and one of them may
 * be the row that arrives.
 *
 * <p>Read off the state the loop ended in, a search that ran out of candidates and one that ran out
 * of budget came out the same. Both ended with rows that had been run and had gone elsewhere, so
 * both said the candidates tried were not witnesses — which over a search that stopped is a claim
 * about the model made on the strength of a limit.
 *
 * <p>The two combinations asked about here are of one model, searched in one run, against runs that
 * all missed alike. What differs between them is how many positions each is about, which is how many
 * the search was left to choose — and so whether the bound was reached. Nothing about the model
 * differs, so what the two answers differ by is the search stopping.
 */
class ASearchThatStoppedSaysSoRatherThanNamingItsLastRefusalTest {

    /**
     * Two decisions and a position free of both.
     *
     * <p>A combination over both decisions leaves the search one position to choose, and the two
     * classes of it are inside the bound. A combination over one decision leaves it two, and the
     * candidates over those run past the bound.
     */
    private static final String SHIPPING = """
            module example.shipping

            data Membership = Premium | Standard

            data Delivery = Express | Regular

            data Fee = Int
                invariant value >= 0

            behavior shippingFee : (member: Membership, delivery: Delivery, rush: Bool) -> Fee
                constructs Fee

            let baseFee (tier: Membership): Int =
                match tier with
                    | Premium -> 0
                    | Standard -> 500

            let expressFee (speed: Delivery): Int =
                match speed with
                    | Express -> 500
                    | Regular -> 0

            let shippingFee (member, delivery, rush) =
                Fee(baseFee(member) + expressFee(delivery))
            """;

    /** A run that did nothing at all, which is a run that missed every combination. */
    private static final Generator.Watched MISSED =
            new Generator.Watched.Ran(Observation.NONE);

    /**
     * A combination whose candidates were all tried says the candidates were not witnesses.
     *
     * <p>Which is something about the model, and it may be said because nothing was left untried
     * behind it.
     */
    @Test
    void aCombinationEveryCandidateMissedSaysTheCandidatesWereNotWitnesses() {
        Generator.GenerationResult filled = fill(Model.of(SHIPPING, "shippingFee"), _ -> MISSED);

        assertEquals(Generator.UnresolvedCombination.Reason.NO_CERTIFIED_WITNESS,
                reasonFor(filled, List.of("member=Premium", "delivery=Express")),
                "one position left to choose, and both of its classes were run: "
                        + filled.unresolved());
    }

    /**
     * The same run of misses at a combination the bound stopped short of says the search stopped.
     *
     * <p>Two positions left to choose is more candidates than a reading is run for. What the ones it
     * did try came to is those candidates' news: offered as the combination's answer it stands for a
     * space this search never entered, and sends a reader to change a rule over a row it never
     * tried.
     */
    @Test
    void aCombinationTheBoundStoppedShortOfSaysTheSearchStopped() {
        Generator.GenerationResult filled = fill(Model.of(SHIPPING, "shippingFee"), _ -> MISSED);

        assertEquals(Generator.UnresolvedCombination.Reason.SEARCH_LIMIT,
                reasonFor(filled, List.of("member=Premium")),
                "two positions left to choose, and the bound was reached before they ran out: "
                        + filled.unresolved());
    }

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
