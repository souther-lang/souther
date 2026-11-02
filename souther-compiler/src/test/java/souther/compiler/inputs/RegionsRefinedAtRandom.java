package souther.compiler.inputs;

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

/**
 * Regions a model reads, and what is said beside them at random, for tests that hold a property to
 * every region and the one made from it by saying more.
 *
 * <p>Five numbers: three held to nought and twenty, one of them only to the even ones, and one to
 * the multiples of a thousand up to five thousand, so that a class is something the region has to
 * keep. More is said by fixing a number or taking a relation between two or three of them in.
 */
final class RegionsRefinedAtRandom {

    private static final String MODEL = """
            module g

            data Small = Int
                invariant value >= 0
                invariant value <= 20

            data Even = Int
                invariant Int.floorMod(value, 2) == 0
                invariant value >= 0
                invariant value <= 20

            data Thousands = Int
                invariant Int.floorMod(value, 1000) == 0
                invariant value >= 0
                invariant value <= 5000

            data Ok

            behavior read : (x: Small, y: Small, w: Small, e: Even, t: Thousands) -> Ok
            """;

    static final List<String> NAMES = List.of("x", "y", "w", "e", "t");

    private record Read(InputDomain input, RuleReadingSource rules) {}

    private static final Read READ = read();

    private RegionsRefinedAtRandom() {}

    /** The region the model's rules alone leave. */
    static SearchRegion region() {
        return READ.input().quantities(READ.rules()).region();
    }

    static NumericTerm.ValueOf term(String spelled) {
        return new NumericTerm.ValueOf(READ.input().positions().stream().map(Position::path)
                .filter(each -> each.toString().equals(spelled)).findFirst()
                .orElseThrow(() -> new AssertionError("no position at " + spelled)));
    }

    static Count at(long value) {
        return new Count(BigDecimal.valueOf(value));
    }

    /**
     * {@code region} with one more thing said of it: a number fixed, or a relation between some of
     * the numbers taken in. Unchanged where the relation cannot be carried.
     */
    static SearchRegion refined(SearchRegion region, Random random) {
        return refined(region, random, new StringBuilder());
    }

    /** The same, saying in {@code said} what was said. */
    static SearchRegion refined(SearchRegion region, Random random, StringBuilder said) {
        if (random.nextInt(3) > 0) {
            String name = NAMES.get(random.nextInt(NAMES.size()));
            long value = name.equals("t") ? 1000L * (random.nextInt(8) - 1) : random.nextInt(26) - 2;
            said.append(" ; ").append(name).append(" = ").append(value);
            return region.given(term(name), at(value));
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
        said.append(" ; ").append(coefs).append(" + c ").append(rel)
                .append(taken instanceof SearchRegion.Assumption.Taken ? "" : " (refused)");
        return taken instanceof SearchRegion.Assumption.Taken it ? it.region() : region;
    }

    private static Read read() {
        Compilation compilation = Compilation.ofSources(List.of(MODEL),
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
