package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.TypeCardinality;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;

import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A region whose reading is settled is shown empty wherever a region it refines was.
 *
 * <p>The word {@link SearchRegion#emptinessIsSettled} gives, held against the regions a model
 * reads. A reader that skips the regions on the way to a whole assignment — the search that goes
 * straight to the end of a walk — is leaning on it: an assignment nothing shows empty is, if the
 * reading of it is settled, one no region on the way to it was shown empty of. The reading may stop
 * short of the end, which is what a rule it could not compose or a round it ran out of does, and
 * then it can show a region empty and a region that says more of the same rules not. That is why
 * the word is asked and not assumed.
 *
 * <p>Regions are written at random over four numbers, each held to nought and twenty, by relations
 * taken in and numbers fixed, and each is set beside the one before it. Both kinds of region are
 * looked for — a coarser one shown empty with a finer one that says so, and a coarser one shown
 * empty with a finer one the reading stopped short of — so the property is asked where it can
 * fail.
 */
class ARegionIsShownEmptyWhereAnythingItRefinesWasIfItsReadingIsSettledTest {

    private static final String FOUR_NUMBERS = """
            module g

            data Small = Int
                invariant value >= 0
                invariant value <= 20

            data Ok

            behavior read : (x: Small, y: Small, z: Small, w: Small) -> Ok
            """;

    private static final List<String> NAMES = List.of("x", "y", "z", "w");
    private static final int REGIONS = 600;

    @Test
    void whereTheFinerReadingIsSettledItShowsEmptyWhatTheCoarserOneDid() {
        Random random = new Random(2980);
        int emptyCoarser = 0;
        int settledFiner = 0;
        for (int i = 0; i < REGIONS; i++) {
            SearchRegion coarser = region();
            for (int step = 0, steps = 1 + random.nextInt(5); step < steps; step++) {
                SearchRegion finer = refined(coarser, random);
                if (coarser.emptiness().isPresent()) {
                    emptyCoarser++;
                    if (finer.emptinessIsSettled()) {
                        settledFiner++;
                        assertTrue(finer.emptiness().isPresent(),
                                () -> "a region shown empty is not shown empty with more said of it"
                                        + " although its reading says it is settled");
                    }
                }
                coarser = finer;
            }
        }
        assertTrue(emptyCoarser > REGIONS / 4,
                "regions shown empty that something was said beside: " + emptyCoarser);
        assertTrue(settledFiner > emptyCoarser / 2,
                "and of them, those whose reading was settled: " + settledFiner);
    }

    /** What is said of every region read here — that a settled reading is a fact about it. */
    @Test
    void aRegionShownEmptyIsSettledWhateverItWasShownBy() {
        SearchRegion empty = region().given(term("x"), at(30));

        assertTrue(empty.emptiness().isPresent(), "x is held to twenty and fixed at thirty");
        assertTrue(empty.emptinessIsSettled());
    }

    @Test
    void aRegionNothingIsSaidOfIsSettled() {
        assertEquals(true, region().emptinessIsSettled());
    }

    private static SearchRegion refined(SearchRegion region, Random random) {
        if (random.nextInt(3) > 0) {
            return region.given(term(NAMES.get(random.nextInt(NAMES.size()))),
                    at(random.nextInt(26) - 2));
        }
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        for (int i = 0, count = 2 + random.nextInt(2); i < count; i++) {
            int weight = 1 + random.nextInt(3);
            coefs.put(term(NAMES.get(random.nextInt(NAMES.size()))),
                    ExactRatio.of(random.nextBoolean() ? weight : -weight));
        }
        Rel rel = List.of(Rel.LE, Rel.LT, Rel.GE, Rel.GT, Rel.EQ).get(random.nextInt(5));
        SearchRegion.Assumption taken = region.assuming(
                new LinearForm<>(ExactRatio.of(random.nextInt(41) - 20), coefs), rel);
        return taken instanceof SearchRegion.Assumption.Taken it ? it.region() : region;
    }

    private static Count at(long value) {
        return new Count(BigDecimal.valueOf(value));
    }

    private static NumericTerm.FromOnePosition term(String spelled) {
        return new NumericTerm.ValueOf(READ.input().positions().stream().map(Position::path)
                .filter(each -> each.toString().equals(spelled)).findFirst()
                .orElseThrow(() -> new AssertionError("no position at " + spelled)));
    }

    private record Read(InputDomain input, RuleReadingSource rules) {}

    private static final Read READ = read();

    private static SearchRegion region() {
        return READ.input().quantities(READ.rules()).region();
    }

    private static Read read() {
        Compilation compilation = Compilation.ofSources(List.of(FOUR_NUMBERS),
                souther.compiler.meta.ModulePath.EMPTY);
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext reading =
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        return new Read(InputDomain.of(sigs.get("read"), reading,
                TypeCardinality.Counts.workedOutIn(reading),
                souther.compiler.carrier.Membership.none()), rules);
    }
}
