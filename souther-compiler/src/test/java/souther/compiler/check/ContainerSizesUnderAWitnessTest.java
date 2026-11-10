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

    /** The body of {@code run}, a walk over a list of decimals from {@code seed} whose step is
     *  {@code step}. */
    private static Core decimalWalk(String seed, String step) {
        Compilation compilation = Compilation.ofSource("""
                module demo
                behavior run : (xs: List<Decimal>) -> Decimal
                let run (xs) = List.fold((acc, x) -> %s, %s, xs)
                """.formatted(step, seed), "Main");
        return compilation.db().ask(new Bodies.CheckedBehavior("demo", "run")).value().body();
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

    private static boolean scalesHaveRoom(String step) {
        return scalesHaveRoom("1.0m", step);
    }

    private static boolean scalesHaveRoom(String seed, String step) {
        Core body = decimalWalk(seed, step);
        Core operation = aDecimalOperation(body);
        return ContainerSizesUnderAWitness.answersOn(body, operation,
                WhatARunMayEndFor.completionApartFromTheClosuresWrittenAtIt(operation),
                node -> Optional.empty(), node -> Optional.empty(),
                node -> node instanceof Core.Read read && read.name().equals("x"));
    }

    /**
     * What a walk carries is at the seed's scale or the step's, by induction. A sum of it and an
     * element goes no further from nought than either; a product of them goes a scale further at
     * every element, so no scale holds on every step.
     */
    @Test
    void aWalkCarriesAScaleOnlyWhereItsStepKeepsIt() {
        assertTrue(scalesHaveRoom("Decimal.add(acc, x)"));
        assertTrue(scalesHaveRoom("Decimal.subtract(acc, x)"));
        assertFalse(scalesHaveRoom("Decimal.multiply(acc, x)"));
    }

    /**
     * A scale held is not room held: a walk whose step multiplies two numbers that each read what
     * it carries doubles the digits at every element, whatever scale it keeps, so a whole number
     * squared or a rounding of a square has no room however the scale stays. A step that adds
     * what it carries to itself, or multiplies it by a number it does not carry, grows the digits
     * by one number's at a time.
     */
    @Test
    void aWalkWhoseDigitsDoubleAtEveryElementHasNoRoomAtAnyScale() {
        assertFalse(scalesHaveRoom("2m", "Decimal.multiply(acc, acc)"));
        assertFalse(scalesHaveRoom("2m",
                "Decimal.round(0, HALF_UP, Decimal.multiply(acc, acc))"));
        assertFalse(scalesHaveRoom("2m",
                "Decimal.multiply(Decimal.add(acc, 1m), Decimal.add(acc, 2m))"));
        assertTrue(scalesHaveRoom("2m", "Decimal.add(acc, acc)"));
        assertTrue(scalesHaveRoom("2m", "Decimal.multiply(acc, 2m)"));
    }

    /** The body of {@code run}, which divides {@code x} by {@code y} at {@code scale}, and adds
     *  what the quotient is to {@code x} where there is one. */
    private static Core quotientBody(String scale) {
        Compilation compilation = Compilation.ofSource("""
                module demo
                behavior run : (x: Decimal, y: Decimal, s: Int) -> Decimal
                let run (x, y, s) = match Decimal.divide(x, y, %s, HALF_UP) with
                    | Decimal as q -> Decimal.add(q, x)
                    | DivisionByZero -> 0.0m
                """.formatted(scale), "Main");
        return compilation.db().ask(new Bodies.CheckedBehavior("demo", "run")).value().body();
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

    private static boolean sumOfTheQuotientHasRoom(String scale) {
        Core body = quotientBody(scale);
        Core sum = callOf(body, ValueName.Stdlib.operation("Decimal", "add"));
        return ContainerSizesUnderAWitness.answersOn(body, sum,
                WhatARunMayEndFor.completionApartFromTheClosuresWrittenAtIt(sum),
                node -> Optional.empty(), node -> Optional.empty(),
                node -> node instanceof Core.Read read
                        && (read.name().equals("x") || read.name().equals("y")));
    }

    /**
     * The number a quotient answers is at the scale it was asked for, which a name an arm gives it
     * is at as well: so a sum of it has room where that scale is written and is one a run has room
     * for, and not where it is handed in or is past what room is shown for.
     */
    @Test
    void theNumberAQuotientAnswersIsAtTheScaleItWasAskedFor() {
        assertTrue(sumOfTheQuotientHasRoom("2"));
        assertFalse(sumOfTheQuotientHasRoom("s"));
        assertFalse(sumOfTheQuotientHasRoom("2147483647"));
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
