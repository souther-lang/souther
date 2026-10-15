package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.carrier.Membership;
import souther.compiler.meaning.AuthoredPointMapping;
import souther.compiler.meaning.Derivation;
import souther.compiler.meaning.WrittenLine;
import souther.compiler.check.Carrier;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.TypeCardinality;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.meta.ModulePath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Towards;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.reach.ComparisonArrival;

import souther.compiler.check.PathReachability;
import souther.compiler.coverage.ConditionOutcomeSite;
import souther.compiler.coverage.ControlPlace;
import souther.compiler.coverage.SeenConditionOutcome;
import souther.compiler.types.ConstructOccurrence;

import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A line goes only where every place it is watched at proved nothing reaches it.
 *
 * <p>One rule may be written into the tree that runs more than once — a library operation
 * evaluating a closure it was handed twice writes the comparison twice — so what arrives at the
 * line is answered once per place. The rule is one: a run through any of the copies is a run
 * through it, so the line is what the model states about all of them.
 *
 * <p><b>Dropped by a proof and never by the absence of one.</b> A walk that could not project what
 * arrives says so ({@link ComparisonArrival.NoProjection}) and restricts nothing beyond what the
 * declarations and the way leave; read as a place where nothing arrives, it would take a line away
 * because this compiler did not look.
 *
 * <p><b>Which is why the quantifier is the whole of this.</b> Every model written today watches
 * each rule in one place, and there the two quantifiers answer alike — so the rule is held here,
 * over the arrivals themselves, rather than waiting for a corpus that happens to write one twice.
 */
class ALineIsDroppedByAProofAtEveryPlaceItIsWatchedTest {

    private static final Carrier WHOLE = new Carrier.Whole();

    /** One position with nothing declared about it, so the declarations reach every line. */
    private static final String ONE = """
            module g

            data Ok

            behavior read : (n: Int) -> Ok
            """;

    private static final Read READ = read();

    private static final TermPath N = READ.input().positions().stream().map(Position::path)
            .filter(each -> each.toString().equals("n")).findFirst().orElseThrow();

    /** {@code n > 10}, read as a line on the values at {@code n}. */
    private static ComparisonAssessment.AtAPosition line() {
        NumericTerm.FromOnePosition n = new NumericTerm.ValueOf(N);
        Cutting cutting = new Cutting(
                new BorderQuantity.OfACoordinate("f", n,
                        TermOrdersFixtures.itself(n, WHOLE)),
                new Level.OnACarrier(WHOLE, new Count(BigDecimal.TEN)),
                new ComparisonClaim.Cut(Towards.BELOW, false), null);
        return new ComparisonAssessment.AtAPosition(cutting, n, null,
                ComparisonAssessment.Places.AT_NO_VALUE, new AuthoredPointMapping.Proven(
                        WrittenLine.THE_COMPARISON, cutting.claim(),
                        Derivation.AComparisonRead.Facing.NOTHING_WRITTEN, true));
    }

    /** Nothing on the way, over what the declarations leave. */
    private static Reachability untouched() {
        return Reachability.untouched(region());
    }

    /** Values that stop short of the line, which is a proof that nothing reaches it. */
    private static ComparisonArrival misses() {
        return new ComparisonArrival.Values(N,
                new NumericDomain.Bounds(null,
                        new Endpoint(new Count(BigDecimal.ONE), true)));
    }

    @Test
    void oneProofAmongSeveralPlacesTakesNoLineAway() {
        ComparisonAssessment read = line();

        assertEquals(read, ComparisonAssessment.narrowedByWhatArrives(read, untouched(), _ -> untouched(),
                        List.of(new ComparisonArrival.NothingArrives(),
                                new ComparisonArrival.NoProjection()),
                        false, reading()),
                "one place nobody could look at is not a place nothing arrives at");
    }

    @Test
    void everyPlaceProvingItTakesTheLineAway() {
        assertInstanceOf(ComparisonAssessment.NothingArrivesAtItsLine.class,
                ComparisonAssessment.narrowedByWhatArrives(line(), untouched(), _ -> untouched(),
                        List.of(new ComparisonArrival.NothingArrives(), misses()), false,
                        reading()),
                "no run answers through the rule at any place it is watched");
    }

    @Test
    void onePlaceReachingItKeepsTheLine() {
        ComparisonAssessment read = line();

        assertEquals(read, ComparisonAssessment.narrowedByWhatArrives(read, untouched(), _ -> untouched(),
                        List.of(new ComparisonArrival.NothingArrives(),
                                new ComparisonArrival.Values(N, NumericDomain.Bounds.OPEN)),
                        false, reading()),
                "a run reaches the line at one of the places the rule is watched at");
    }

    /**
     * What a body is divided by is the reading as the rows corrected it. A row at a comparison
     * shows wrong a proof that nothing arrives there ({@link
     * souther.compiler.check.PathReachability.Answers#asRunWith}), and a division made from the
     * reading before the run would drop the line by the proof the run took back.
     */
    @Test
    void aBodyIsDividedByWhatArrivesOnceTheRowsHaveRun() {
        Compilation compilation = Compilation.ofSources(List.of("""
                module g

                data Small
                data Large

                behavior size : (n: Int) -> Small | Large
                let size (n) = if n > 10 then Large else Small
                """), ModulePath.EMPTY);
        String module = compilation.modules().get(0);

        assertNotNull(compilation.db().ask(new Adequacy.Divided(module, "size")).value(),
                "the body is divided");
        assertTrue(compilation.db().isComputed(new Adequacy.ArrivedAtComparisons(module)),
                "by what arrives once the rows have run, at the comparisons alone");
    }

    /**
     * An application's line is dropped by what arrives at it as a comparison's is, and a row
     * recorded answering there came to it. So a proof that nothing arrives at it is taken back
     * like a comparison's, though an application files no way out of it among the places.
     */
    @Test
    void aRowAtAnApplicationTakesBackThatNothingArrivesThere() {
        Compilation compilation = Compilation.ofSources(List.of("""
                module g

                data Small
                data Large

                behavior size : (xs: List<Int>) -> Small | Large
                let size (xs) = if List.isEmpty(xs) then Small else Large
                """), ModulePath.EMPTY);
        String module = compilation.modules().get(0);
        PathReachability.Answers read =
                compilation.db().ask(new Adequacy.PathReached(module)).value().get("size");
        Set<ConstructOccurrence> comparisons = new LinkedHashSet<>();
        read.found().keySet().forEach(place -> {
            if (place instanceof ControlPlace.Outcome outcome) {
                comparisons.add(outcome.occurrence());
            }
        });
        Map.Entry<ConstructOccurrence, ConditionOutcomeSite> application =
                read.recordedAt().entrySet().stream()
                        .filter(each -> !comparisons.contains(each.getKey()))
                        .findFirst().orElseThrow(() -> new AssertionError(
                                "the emptiness check is an application: " + read.recordedAt()));
        Map<ConstructOccurrence, ComparisonArrival> nothing = new LinkedHashMap<>(read.arriving());
        nothing.put(application.getKey(), new ComparisonArrival.NothingArrives());
        PathReachability.Answers proven = new PathReachability.Answers(read.numbering(),
                read.found(), nothing, read.recordedAt());

        PathReachability.Answers.AsRun run = proven.asRunWith(Set.of(),
                Set.of(new SeenConditionOutcome(application.getValue(), false)));

        assertEquals(Set.of(application.getKey()), run.contradicted().emptyArrivals(),
                "a row answered there, so it came there");
        assertInstanceOf(ComparisonArrival.NoProjection.class,
                run.answers().arrivalAt(application.getKey()), "and what arrives restricts nothing");
    }

    private static InputReading reading() {
        return READ.input().reading(READ.rules());
    }

    private static SearchRegion region() {
        return READ.input().quantities(READ.rules()).region();
    }

    /** The model read once for the whole class: a region is made of the input and its rules. */
    private record Read(InputDomain input, RuleReadingSource rules) {}

    private static Read read() {
        Compilation compilation = Compilation.ofSources(List.of(ONE), ModulePath.EMPTY);
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext context =
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES);
        return new Read(InputDomain.of(sigs.get("read"), context,
                TypeCardinality.Counts.workedOutIn(context), Membership.none()), rules);
    }
}
