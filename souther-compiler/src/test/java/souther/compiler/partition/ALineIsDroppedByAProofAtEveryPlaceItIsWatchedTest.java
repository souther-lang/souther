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
        assertTrue(compilation.db().isComputed(new Adequacy.ArrivedAtLines(module)),
                "by what arrives once the rows have run, where lines are drawn and nowhere else");
    }

    /**
     * An application's line is dropped by what arrives at it as a comparison's is, and a row
     * recorded answering there came to it. So a proof that nothing arrives at it is taken back
     * like a comparison's, though an application files no way out of it among the places.
     */
    @Test
    void aRowAtAnApplicationTakesBackThatNothingArrivesThere() {
        PathReachability.Answers.AsRun run = APPLIED.proving(
                new ComparisonArrival.NothingArrives()).asRunWith(Set.of(), APPLIED.aRowCame());

        assertEquals(Set.of(APPLIED.construct()), run.contradicted().emptyArrivals(),
                "a row answered there, so it came there");
        assertInstanceOf(ComparisonArrival.NoProjection.class,
                run.answers().arrivals().arrivalAt(APPLIED.construct()),
                "and what arrives restricts nothing");
    }

    /**
     * What the run takes back is what the line is assessed by. A line dropped because nothing
     * arrives where it is drawn is kept once a row has come there, and a line dropped because what
     * arrives does not reach it stays dropped: the run says a row came, not which values did.
     */
    @Test
    void aLineIsKeptWhereARowCameToWhatWasProvenEmptyAndOnlyThere() {
        ComparisonArrival proven = APPLIED.proving(new ComparisonArrival.NothingArrives())
                .arrivals().arrivalAt(APPLIED.construct());
        ComparisonArrival ran = APPLIED.proving(new ComparisonArrival.NothingArrives())
                .asRunWith(Set.of(), APPLIED.aRowCame()).answers().arrivals()
                .arrivalAt(APPLIED.construct());
        ComparisonArrival missedAndRan = APPLIED.proving(misses())
                .asRunWith(Set.of(), APPLIED.aRowCame()).answers().arrivals()
                .arrivalAt(APPLIED.construct());

        assertInstanceOf(ComparisonAssessment.NothingArrivesAtItsLine.class,
                assessedOn(proven), "before the run nothing arrives, and the line goes");
        assertEquals(line(), assessedOn(ran),
                "a row came there, so the proof the line went by is gone and the line stays");
        assertInstanceOf(ComparisonAssessment.NothingArrivesAtItsLine.class,
                assessedOn(missedAndRan),
                "and what arrives stopping short of the line still takes it away");
    }

    /** {@link #line()} as the one place it is watched at has {@code arrives} arriving there. */
    private static ComparisonAssessment assessedOn(ComparisonArrival arrives) {
        return ComparisonAssessment.narrowedByWhatArrives(line(), untouched(), _ -> untouched(),
                List.of(arrives), false, reading());
    }

    /**
     * An application a line is drawn at — the emptiness check in {@code size} — read off a
     * compile, with what arrives at it set by hand.
     *
     * @param read      the reading the compile made
     * @param construct the application, which files no way out of it among the places
     * @param site      where a row coming to it is recorded
     */
    private record Applied(PathReachability.Answers read, ConstructOccurrence construct,
                           ConditionOutcomeSite site) {

        /** The reading with {@code arriving} at the application, as the compile made it
         *  everywhere else. */
        PathReachability.Answers proving(ComparisonArrival arriving) {
            PathReachability.Arrivals compiled = read.arrivals();
            Map<ConstructOccurrence, ComparisonArrival> arrivals =
                    new LinkedHashMap<>(compiled.arriving());
            arrivals.put(construct, arriving);
            return new PathReachability.Answers(read.numbering(), read.found(),
                    new PathReachability.Arrivals(compiled.numbering(), arrivals,
                            compiled.recordedAt()));
        }

        /** A row recorded answering there. */
        Set<SeenConditionOutcome> aRowCame() {
            return Set.of(new SeenConditionOutcome(site, false));
        }
    }

    private static final Applied APPLIED = applied();

    private static Applied applied() {
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
                read.arrivals().recordedAt().entrySet().stream()
                        .filter(each -> !comparisons.contains(each.getKey()))
                        .findFirst().orElseThrow(() -> new AssertionError(
                                "the emptiness check is an application: "
                                        + read.arrivals().recordedAt()));
        return new Applied(read, application.getKey(), application.getValue());
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
