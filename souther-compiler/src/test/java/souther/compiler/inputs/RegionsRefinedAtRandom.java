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
 * <p>Numbers of several kinds: three held to nought and twenty, one only to the even ones, one only
 * to the multiples of a thousand up to five thousand, those a sum's two cases hold, and what a list
 * holds. A class is something the region has to keep and a case is something it has to keep
 * apart. More is said by fixing a number, taking a relation between some of them in, taking one
 * number against a value in, or holding one apart from a value.
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

            data Circle = { r: Small }
            data Rect = { w: Small, h: Small }
            data Shape = Circle | Rect

            data Ok

            behavior read : (x: Small, y: Small, w: Small, e: Even, t: Thousands, s: Shape,
                             xs: List<Small>, name: String, ns: List<Int>) -> Ok
            """;

    /** The numbers that are fixed and related, by where they stand. */
    static final List<String> NAMES = List.of("x", "y", "w", "e", "t", "s@Circle.r", "s@Rect.w",
            "s@Rect.h", "xs[*]");

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
                .orElseThrow(() -> new AssertionError("no position at " + spelled + " among "
                        + READ.input().positions().stream().map(Position::path).toList())));
    }

    static Count at(long value) {
        return new Count(BigDecimal.valueOf(value));
    }

    /** The numbers taken of a position and not the value it holds, which are fixed and related
     *  beside the numbers above: a remainder, which narrows a class, and the size of the list. */
    private static final List<String> TAKEN = List.of("x%3", "e%4", "length(xs)");

    /** Every number a region is asked to run: the ones above and the ones taken of a position. */
    static final List<String> EVERY_NUMBER = java.util.stream.Stream.concat(
            NAMES.stream(), TAKEN.stream()).toList();

    /** Any of the numbers above, or one of those taken of a position. */
    static NumericTerm.FromOnePosition anyTerm(String spelled) {
        return switch (spelled) {
            case "x%3" -> remainder("x", 3);
            case "e%4" -> remainder("e", 4);
            case "length(xs)" -> lengthOf("xs");
            default -> term(spelled);
        };
    }

    private static NumericTerm.FromOnePosition remainder(String position, int divisor) {
        TermPath at = term(position).position();
        NumericTerm.FromOnePosition made = NumericTerm.TakenOf.asItStands(
                souther.compiler.types.ValueName.Stdlib.operation("Int", "floorMod"), at,
                souther.compiler.semantics.TakenArguments.at(1, BigDecimal.valueOf(divisor)),
                READ.input().at(at).type(), READ.rules().inners(), READ.rules().symbols());
        if (made == null) {
            throw new AssertionError("no remainder by " + divisor + " of " + position);
        }
        return made;
    }

    /**
     * Numbers taken of a position that no property here is held for: the sum of a list, a
     * quotient, and the length of a string. A region is asked about them and says no.
     */
    static List<NumericTerm.FromOnePosition> notHeldFor() {
        TermPath ns = TermPath.of("ns");
        TermPath x = term("x").position();
        TermPath name = term("name").position();
        return List.of(
                taken(souther.compiler.types.ValueName.Stdlib.operation("List", "sum"), ns,
                        souther.compiler.semantics.TakenArguments.NONE),
                taken(souther.compiler.types.ValueName.Stdlib.operation("Int", "truncatingDivide"),
                        x, souther.compiler.semantics.TakenArguments.at(1, BigDecimal.valueOf(3))),
                taken(souther.compiler.types.ValueName.Stdlib.operation("String", "length"), name,
                        souther.compiler.semantics.TakenArguments.NONE));
    }

    private static NumericTerm.FromOnePosition taken(
            souther.compiler.types.ValueName.Stdlib operation, TermPath at,
            souther.compiler.semantics.TakenArguments arguments) {
        NumericTerm.FromOnePosition made = NumericTerm.TakenOf.asItStands(operation, at, arguments,
                READ.input().at(at).type(), READ.rules().inners(), READ.rules().symbols());
        if (made == null) {
            throw new AssertionError("no " + operation + " of " + at);
        }
        return made;
    }

    private static NumericTerm.FromOnePosition lengthOf(String position) {
        TermPath at = term(position).position();
        souther.compiler.types.Type type = READ.input().at(at).type();
        NumericTerm.FromOnePosition made = NumericTerm.TakenOf.asItStands(
                souther.compiler.check.NumericMeasures.takenOf(type, READ.rules().inners()),
                at, type, READ.rules().inners(), READ.rules().symbols());
        if (made == null) {
            throw new AssertionError("no length of " + position);
        }
        return made;
    }

    /** A value the number called {@code name} may well be, and now and then one it cannot be. */
    static long valueFor(String name, Random random) {
        return switch (name) {
            case "t" -> 1000L * (random.nextInt(8) - 1);
            case "x%3" -> random.nextInt(4);
            case "e%4" -> random.nextInt(5);
            case "length(xs)" -> random.nextInt(5);
            default -> random.nextInt(26) - 2;
        };
    }

    private static String anyName(Random random) {
        int at = random.nextInt(NAMES.size() + TAKEN.size());
        return at < NAMES.size() ? NAMES.get(at) : TAKEN.get(at - NAMES.size());
    }

    static SearchRegion refined(SearchRegion region, Random random) {
        return refined(region, random, new StringBuilder());
    }

    /**
     * {@code region} with one more thing said of it, said in {@code said}: a number fixed, a
     * relation between some of the numbers taken in, one number taken against a value, or one held
     * apart from a value. Unchanged where the relation cannot be carried.
     */
    static SearchRegion refined(SearchRegion region, Random random, StringBuilder said) {
        int how = random.nextInt(8);
        String name = anyName(random);
        if (how < 3) {
            long value = valueFor(name, random);
            said.append(" ; ").append(name).append(" = ").append(value);
            return region.given(anyTerm(name), at(value));
        }
        if (how == 3) {
            long value = valueFor(name, random);
            Rel rel = List.of(Rel.LE, Rel.LT, Rel.GE, Rel.GT).get(random.nextInt(4));
            said.append(" ; ").append(name).append(' ').append(rel).append(' ').append(value);
            return region.assuming(anyTerm(name), at(value), rel);
        }
        if (how == 4) {
            long value = valueFor(name, random);
            said.append(" ; ").append(name).append(" /= ").append(value);
            return region.apartFrom(anyTerm(name), at(value));
        }
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        for (int i = 0, count = 2 + random.nextInt(2); i < count; i++) {
            int weight = 1 + random.nextInt(3);
            coefs.put(anyTerm(anyName(random)),
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
