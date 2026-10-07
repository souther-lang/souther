package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
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
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.reach.ComparisonArrival;

import java.math.BigDecimal;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

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
                ComparisonAssessment.Places.AT_NO_VALUE);
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

        assertEquals(read, ComparisonAssessment.narrowedByWhatArrives(read, untouched(),
                        List.of(new ComparisonArrival.NothingArrives(),
                                new ComparisonArrival.NoProjection()),
                        false),
                "one place nobody could look at is not a place nothing arrives at");
    }

    @Test
    void everyPlaceProvingItTakesTheLineAway() {
        assertInstanceOf(ComparisonAssessment.NothingArrivesAtItsLine.class,
                ComparisonAssessment.narrowedByWhatArrives(line(), untouched(),
                        List.of(new ComparisonArrival.NothingArrives(), misses()), false),
                "no run answers through the rule at any place it is watched");
    }

    @Test
    void onePlaceReachingItKeepsTheLine() {
        ComparisonAssessment read = line();

        assertEquals(read, ComparisonAssessment.narrowedByWhatArrives(read, untouched(),
                        List.of(new ComparisonArrival.NothingArrives(),
                                new ComparisonArrival.Values(N, NumericDomain.Bounds.OPEN)),
                        false),
                "a run reaches the line at one of the places the rule is watched at");
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
        return new Read(InputDomain.of(sigs.get("read"),
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES)), rules);
    }
}
