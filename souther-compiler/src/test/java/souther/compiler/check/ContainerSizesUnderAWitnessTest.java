package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.abort.GetsPast;
import souther.compiler.core.Core;
import souther.compiler.types.ValueName;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a union a walk takes at each element answers on a run whose input sets hold as many as
 * the caller says, read by induction on what the walk carries.
 *
 * <p>The walk is the one a body writes, read off the tree a behavior is checked as; how many the
 * list and each set it holds have is handed in, as a witness would be.
 */
class ContainerSizesUnderAWitnessTest {

    private static final BigInteger HALF_OF_WHAT_A_SET_HOLDS = BigInteger.TWO.pow(30);

    /** The body of {@code run}, taking {@code xs}, a list of sets, and answering {@code body}. */
    private static Core bodyOf(String body) {
        Compilation compilation = Compilation.ofSource("""
                module demo
                data Ids = Set<String>
                behavior run : (xs: List<Ids>) -> Int
                let run (xs) = %s
                """.formatted(body), "Main");
        return compilation.db().ask(new Bodies.CheckedBehavior("demo", "run")).value().body();
    }

    /** Every union under {@code body}, outermost first. */
    private static List<Core> unions(Core body) {
        List<Core> out = new ArrayList<>();
        collect(body, out);
        return out;
    }

    private static void collect(Core e, List<Core> out) {
        Core node = Core.withoutStanding(e);
        AnOperationApplied applied = AnOperationApplied.of(node);
        if (applied != null && applied.operation().equals(
                souther.compiler.types.ValueName.Stdlib.operation("Set", "union"))) {
            out.add(node);
        }
        Core.forEachChild(node, child -> collect(child, out));
    }

    /** The list holds {@code list} sets, and each set an element hands the step holds
     *  {@code each}. */
    private static Function<Core, Optional<BigInteger>> holding(BigInteger list, BigInteger each) {
        return node -> switch (node) {
            case Core.Read read when read.name().equals("xs") -> Optional.of(list);
            case Core.FieldAccess _ -> Optional.of(each);
            default -> Optional.empty();
        };
    }

    private static boolean answers(Core body, Core union,
                                   Function<Core, Optional<BigInteger>> witness) {
        GetsPast completion = WhatARunMayEndFor.completionApartFromTheClosuresWrittenAtIt(union);
        return completion instanceof GetsPast.WhereTheAnswerFits fits
                && ContainerSizesUnderAWitness.answersOn(body, union, fits, witness,
                        node -> Optional.empty(), node -> false);
    }

    /** The body of one behavior for each of {@code expressions}, compiled together: each answers a
     *  decimal over {@code x} and {@code y}, decimals, {@code n} and {@code s}, whole numbers, and
     *  {@code xs}, a list of decimals. */
    private static List<Core> bodiesOf(String... expressions) {
        StringBuilder source = new StringBuilder("module demo\n");
        for (int at = 0; at < expressions.length; at++) {
            source.append("""
                    behavior run%1$d : (x: Decimal, y: Decimal, n: Int, s: Int, xs: List<Decimal>) -> Decimal
                    let run%1$d (x, y, n, s, xs) = %2$s
                    """.formatted(at, expressions[at]));
        }
        Compilation compilation = Compilation.ofSource(source.toString(), "Main");
        List<Core> bodies = new ArrayList<>();
        for (int at = 0; at < expressions.length; at++) {
            bodies.add(compilation.db().ask(new Bodies.CheckedBehavior("demo", "run" + at))
                    .value().body());
        }
        return bodies;
    }

    /** The first operation under {@code e} that answers where the scales have room. */
    private static Core aDecimalOperation(Core e) {
        Core node = Core.withoutStanding(e);
        if (WhatARunMayEndFor.completionApartFromTheClosuresWrittenAtIt(node)
                instanceof GetsPast.WhereTheScalesHaveRoom) {
            return node;
        }
        Core[] found = {null};
        Core.forEachChild(node, child -> {
            if (found[0] == null) {
                found[0] = aDecimalOperation(child);
            }
        });
        return found[0];
    }

    /** The first call of {@code operation} under {@code e}. */
    private static Core callOf(Core e, ValueName operation) {
        Core node = Core.withoutStanding(e);
        AnOperationApplied applied = AnOperationApplied.of(node);
        if (applied != null && applied.operation().equals(operation)) {
            return node;
        }
        Core[] found = {null};
        Core.forEachChild(node, child -> {
            if (found[0] == null) {
                found[0] = callOf(child, operation);
            }
        });
        return found[0];
    }

    /** Whether the scales {@code operation}, an operation under {@code body}, is handed have
     *  room, as a run of a row, whose decimals are {@code x}, {@code y} and what a walk is handed
     *  as {@code e}, leaves them. */
    private static boolean hasRoom(Core body, Core operation) {
        return ContainerSizesUnderAWitness.answersOn(body, operation,
                WhatARunMayEndFor.completionApartFromTheClosuresWrittenAtIt(operation),
                node -> Optional.empty(), node -> Optional.empty(),
                node -> node instanceof Core.Read read
                        && List.of("x", "y", "e").contains(read.name()));
    }

    private static final ValueName ADD = ValueName.Stdlib.operation("Decimal", "add");

    /** Whether the sum {@code expression} is the first operand of has room. */
    private static List<Boolean> sumsHaveRoom(String... operands) {
        String[] sums = new String[operands.length];
        for (int at = 0; at < operands.length; at++) {
            sums[at] = "Decimal.add(" + operands[at] + ", y)";
        }
        List<Boolean> out = new ArrayList<>();
        for (Core body : bodiesOf(sums)) {
            out.add(hasRoom(body, callOf(body, ADD)));
        }
        return out;
    }

    /**
     * What the library declares of an operation says what scale its answer is at: a negation keeps
     * its operand's, a whole number widened to a decimal has none, the greater of two is one of
     * them, and a rounding is at the places it is asked for, a whole number the call writes out.
     * So a sum of one has room wherever those scales do, and not where the places asked for are
     * not written.
     */
    @Test
    void theScaleOfAnOperandIsReadOffWhatTheLibraryDeclaresOfItsOperation() {
        assertEquals(List.of(true, true, true, true, true, true, true, true, true, false),
                sumsHaveRoom("-x", "Decimal.fromInt(3)", "Decimal.fromInt(n)",
                        "Decimal.max(x, y)", "Decimal.clamp(x, y, x)",
                        "Decimal.max(-x, Decimal.fromInt(n))", "Decimal.round(2, HALF_UP, x)",
                        "Decimal.abs(x)", "Decimal.multiply(Decimal.add(x, 1.5m), y)",
                        "Decimal.round(s, HALF_UP, x)"));
    }

    /**
     * The number a quotient answers is at the scale it was asked for, which a name an arm gives it
     * is at as well: so a sum of it has room where that scale is written and is one a run has room
     * for, and not where it is handed in or is past what room is shown for. A zero divisor is a
     * case of the answer and adds nothing to what is asked.
     */
    @Test
    void theNumberAQuotientAnswersIsAtTheScaleItWasAskedFor() {
        String divided = "match Decimal.divide(x, y, %s, HALF_UP) with"
                + " | Decimal as q -> Decimal.add(q, x) | DivisionByZero -> 0.0m";
        List<Boolean> out = new ArrayList<>();
        for (Core body : bodiesOf(divided.formatted("2"), divided.formatted("s"),
                divided.formatted("2147483647"))) {
            out.add(hasRoom(body, callOf(body, ADD)));
        }
        assertEquals(List.of(true, false, false), out);
    }

    private static List<Boolean> walksHaveRoom(String seed, String... steps) {
        String[] walks = new String[steps.length];
        for (int at = 0; at < steps.length; at++) {
            walks[at] = "List.fold((acc, e) -> " + steps[at] + ", " + seed + ", xs)";
        }
        List<Boolean> out = new ArrayList<>();
        for (Core body : bodiesOf(walks)) {
            out.add(hasRoom(body, aDecimalOperation(body)));
        }
        return out;
    }

    /**
     * What a walk carries is at the seed's scale or the step's, by induction. A sum of it and an
     * element goes no further from nought than either; a product of them goes a scale further at
     * every element, so no scale holds on every step.
     */
    @Test
    void aWalkCarriesAScaleOnlyWhereItsStepKeepsIt() {
        assertEquals(List.of(true, true, false), walksHaveRoom("1.0m", "Decimal.add(acc, e)",
                "Decimal.subtract(acc, e)", "Decimal.multiply(acc, e)"));
    }

    /**
     * A scale held is not room held: what a walk carries has room only where its step adds parts
     * to it, which grow its digits by those of the number of elements and no more. What it
     * carries added to itself, multiplied, squared or rounded can grow them at every element past
     * what a representation holds whatever scale it keeps — a number of any size doubles, and a
     * whole number squared or a rounding of a square has no room however the scale stays.
     */
    @Test
    void aWalkHasRoomOnlyWhereItsStepAddsPartsToWhatItCarries() {
        assertEquals(List.of(true, true, true, true, true, true, true), walksHaveRoom("2m",
                "Decimal.add(acc, e)", "Decimal.add(e, acc)", "Decimal.subtract(acc, e)",
                "Decimal.add(Decimal.subtract(acc, e), 2m)",
                "Decimal.add(acc, Decimal.multiply(e, e))",
                "-Decimal.add(acc, e)", "if e > 0m then Decimal.add(acc, e) else acc"));
        assertEquals(List.of(false, false, false, false, false, false), walksHaveRoom("2m",
                "Decimal.add(acc, acc)", "Decimal.multiply(acc, 2m)",
                "Decimal.multiply(acc, Decimal.round(0, HALF_UP, e))",
                "Decimal.multiply(acc, acc)",
                "Decimal.round(0, HALF_UP, Decimal.multiply(acc, acc))",
                "Decimal.multiply(Decimal.add(acc, 1m), Decimal.add(acc, 2m))"));
    }

    private static final String WALK =
            "Set.size(List.fold((acc, x) -> Set.union(acc, x.value), Set.empty, xs))";

    /**
     * What the walk carries holds no more than the sets it was handed together: two of one
     * element each fit, two of half of what a set holds come to one past it, and one such fits.
     */
    @Test
    void whatTheWalkCarriesHoldsNoMoreThanTheSetsItWasHanded() {
        Core body = bodyOf(WALK);
        Core union = unions(body).getFirst();

        assertTrue(answers(body, union, holding(BigInteger.TWO, BigInteger.ONE)));
        assertFalse(answers(body, union, holding(BigInteger.TWO, HALF_OF_WHAT_A_SET_HOLDS)));
        assertTrue(answers(body, union, holding(BigInteger.ONE, HALF_OF_WHAT_A_SET_HOLDS)));
    }

    /** A step that joins what it carries to something made of it puts in no number of elements
     *  of its own, and nothing is said of the walk, however few the sets hold. */
    @Test
    void aStepJoiningWhatItCarriesToItselfIsNotRead() {
        Core body = bodyOf("Set.size(List.fold((acc, x) -> Set.union(acc, Set.union(acc, x.value)),"
                + " Set.empty, xs))");

        assertEquals(2, unions(body).size());
        assertFalse(answers(body, unions(body).getFirst(),
                holding(BigInteger.ONE, BigInteger.ONE)));
    }

    /**
     * Where how many the list holds is not handed in, it holds no more than any list does: sets of
     * one element each come together to no more than a set holds, and sets of two may come past
     * it.
     */
    @Test
    void aListOfNoKnownSizeHoldsNoMoreThanAnyListDoes() {
        Core body = bodyOf(WALK);
        Function<Integer, Function<Core, Optional<BigInteger>>> eachHolding = each -> node ->
                node instanceof Core.FieldAccess ? Optional.of(BigInteger.valueOf(each))
                        : Optional.empty();

        assertTrue(answers(body, unions(body).getFirst(), eachHolding.apply(1)));
        assertFalse(answers(body, unions(body).getFirst(), eachHolding.apply(2)));
    }
}
