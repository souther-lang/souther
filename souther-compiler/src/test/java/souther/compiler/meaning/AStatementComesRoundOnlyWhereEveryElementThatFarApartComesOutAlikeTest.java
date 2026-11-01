package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Random;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a statement is said to come round over an element ({@link TheElementComesRound#in}), it
 * comes out on every element as it does on the element as many past it as is said; where only
 * its remainders are ({@link TheElementComesRound#inItsRemainders}), every remainder weighing the
 * element leaves the same on the two.
 *
 * <p>Held against the statement worked out here at every element of a turn either side of nought,
 * with the other element and the input's number at a few values: every dividend is a form of
 * whole numbers, so two elements a turn apart are compared everywhere once they are compared over
 * one turn. Statements are drawn at random from a fixed seed: comparisons of
 * remainders of the element and the number by divisors of their own, the element weighed by
 * whole numbers below nought and above it, nought among them; the element weighed by half of
 * itself, weighed outside a remainder, and another element beside it, which a statement coming
 * round cannot hold; held together and as alternatives, and denied. Both kinds are drawn, so each
 * answer is asked of statements that come round and of statements that do not.
 */
class AStatementComesRoundOnlyWhereEveryElementThatFarApartComesOutAlikeTest {

    private static final NumericTerm X = new NumericTerm.ValueOf(TermPath.of("x"));
    private static final Quantity INPUT = new DecisionAtom.OfTheInput(X);
    private static final Quantity.OfABinding ELEMENT = element(0);
    private static final Quantity.OfABinding OTHER = element(1);
    private static final ValueName FLOOR_MOD = ValueName.Stdlib.operation("Int", "floorMod");

    @Test
    void aStatementSaidToComeRoundComesOutAlikeThatFarApart() {
        Random random = new Random(2937);
        int round = 0;
        int refused = 0;
        for (int drawn = 0; drawn < 1000; drawn++) {
            Proposition stated = statement(random, 3);
            Optional<TheElementComesRound> said = TheElementComesRound.in(stated);
            if (said.isEmpty()) {
                refused++;
                continue;
            }
            round++;
            Quantity.OfABinding element = said.get().element();
            assertEquals(Set.of(element), bindingsIn(stated, false), () -> stated.spelling()
                    + " weighs one element, which is the one a reader puts a value at");
            long every = said.get().every().longValueExact();
            for (long n = -every; n < every; n++) {
                for (long beside = -1; beside <= 1; beside++) {
                    for (long x = -2; x <= 2; x++) {
                        Values at = Values.of(element, n, beside, x);
                        Values past = Values.of(element, n + every, beside, x);
                        assertEquals(holds(stated, at), holds(stated, past),
                                () -> stated.spelling() + " at " + at + " and " + past);
                    }
                }
            }
        }
        assertTrue(round > 0 && refused > 0, round + " come round, " + refused + " do not");
    }

    @Test
    void theRemaindersOfAStatementSaidToComeRoundLeaveTheSameThatFarApart() {
        Random random = new Random(2938);
        int round = 0;
        int refused = 0;
        // What a remainder leaves is the remainder's alone: each is asked once of each turn.
        Set<List<Object>> asked = new HashSet<>();
        for (int drawn = 0; drawn < 1000; drawn++) {
            Proposition stated = statement(random, 3);
            Optional<TheElementComesRound> said = TheElementComesRound.inItsRemainders(stated);
            if (said.isEmpty()) {
                refused++;
                continue;
            }
            round++;
            Quantity.OfABinding element = said.get().element();
            assertEquals(Set.of(element), bindingsIn(stated, true), () -> stated.spelling()
                    + " weighs one element in its remainders, which is the one a reader puts a"
                    + " value at");
            long every = said.get().every().longValueExact();
            List<Quantity.RemainderOfADividend> remainders = new ArrayList<>();
            remaindersIn(stated, remainders);
            for (Quantity.RemainderOfADividend each : remainders) {
                if (!each.dividend().coefs().containsKey(element)
                        || !asked.add(List.of(each, element, every))) {
                    continue;
                }
                Twice twice = Twice.of(each);
                for (long n = -every; n < every; n++) {
                    for (long beside = -1; beside <= 1; beside++) {
                        for (long x = -2; x <= 2; x++) {
                            Values at = Values.of(element, n, beside, x);
                            Values past = Values.of(element, n + every, beside, x);
                            assertEquals(twice.leaves(at), twice.leaves(past),
                                    () -> each + " at " + at + " and " + past);
                        }
                    }
                }
            }
        }
        assertTrue(round > 0 && refused > 0, round + " come round, " + refused + " do not");
    }

    private static Quantity.OfABinding element(int slot) {
        return new Quantity.OfABinding(
                new BindingId(new BindingOwner.OfValue("demo", "f"), slot), List.of(), Type.INT,
                Optional.empty(), Optional.of(new Quantity.AWholeNumberInTurn(
                        LinearForm.constant(ExactRatio.ZERO),
                        new LinearForm<>(ExactRatio.ZERO, Map.of(X, ExactRatio.ONE)))));
    }

    private static Proposition statement(Random random, int depth) {
        int kind = random.nextInt(depth == 0 ? 1 : 4);
        if (kind == 0) {
            return comparison(random);
        }
        List<Proposition> parts = new ArrayList<>();
        for (int at = 0; at < 2 + random.nextInt(2); at++) {
            parts.add(statement(random, depth - 1));
        }
        Proposition joined = kind == 1 ? Proposition.all(parts) : Proposition.any(parts);
        return kind == 3 ? joined.denied() : joined;
    }

    /** A comparison of a remainder or two, now and then of something a statement coming round
     *  cannot hold. */
    private static Proposition comparison(Random random) {
        Map<Quantity, ExactRatio> coefs = new LinkedHashMap<>();
        for (int at = 0; at < 1 + random.nextInt(2); at++) {
            coefs.put(remainder(random), ExactRatio.of(random.nextInt(5) - 2));
        }
        switch (random.nextInt(12)) {
            case 0 -> coefs.put(ELEMENT, ExactRatio.ONE);
            case 1 -> coefs.put(INPUT, ExactRatio.of(random.nextInt(3) - 1));
            default -> { }
        }
        coefs.values().removeIf(each -> each.signum() == 0);
        if (coefs.isEmpty()) {
            coefs.put(remainder(random), ExactRatio.ONE);
        }
        Relation.OneWay<Quantity> one = Relation.OneWay.of(
                new LinearForm<>(ExactRatio.of(random.nextInt(7) - 3), coefs),
                new Rel[] {Rel.GE, Rel.GT, Rel.EQ}[random.nextInt(3)]);
        return new Proposition.Compared(new Relation.Affine(one.form(), one.proposition()),
                one.holds() == random.nextBoolean());
    }

    /** {@code floorMod(w·n + v·x + c, d)}: the element by a whole number, nought among them, and
     *  now and then by a half or beside another element. */
    private static Quantity remainder(Random random) {
        Map<Quantity, ExactRatio> dividend = new LinkedHashMap<>();
        int odd = random.nextInt(15);
        dividend.put(ELEMENT, odd == 0 ? ExactRatio.of(BigInteger.ONE, BigInteger.TWO)
                : ExactRatio.of(random.nextInt(7) - 3));
        dividend.put(INPUT, ExactRatio.of(random.nextInt(3) - 1));
        if (odd == 1) {
            dividend.put(OTHER, ExactRatio.ONE);
        }
        dividend.values().removeIf(each -> each.signum() == 0);
        if (dividend.isEmpty()) {
            dividend.put(INPUT, ExactRatio.ONE);
        }
        return new Quantity.RemainderOfADividend(FLOOR_MOD,
                new LinearForm<>(ExactRatio.of(random.nextInt(9) - 4), dividend),
                BigInteger.valueOf(1 + random.nextInt(6)));
    }

    /** The values of the two elements and of the input's number. */
    private record Values(long element, long other, long x) {

        /** {@code shifted} at {@code at}, the other element at {@code beside}. */
        static Values of(Quantity.OfABinding shifted, long at, long beside, long x) {
            return shifted.equals(ELEMENT) ? new Values(at, beside, x)
                    : new Values(beside, at, x);
        }

        long of(Quantity each) {
            if (each.equals(ELEMENT)) {
                return element;
            }
            if (each.equals(OTHER)) {
                return other;
            }
            if (each.equals(INPUT)) {
                return x;
            }
            throw new AssertionError("no such number is drawn: " + each);
        }
    }

    private static boolean holds(Proposition stated, Values at) {
        return switch (stated) {
            case Proposition.Always(boolean holds) -> holds;
            case Proposition.All(var parts, var _) ->
                    parts.stream().allMatch(each -> holds(each, at));
            case Proposition.Any(var parts, var _) ->
                    parts.stream().anyMatch(each -> holds(each, at));
            case Proposition.Compared(Relation.Affine affine, boolean holds, var _) ->
                    affine.proposition().holds(sum(affine.form(), at).signum()) == holds;
            default -> throw new AssertionError("no such statement is drawn: " + stated);
        };
    }

    /** What {@code form} comes to at {@code at}, times two: halves are whole there. */
    private static BigInteger sum(LinearForm<Quantity> form, Values at) {
        ExactRatio out = form.constant();
        for (Map.Entry<Quantity, ExactRatio> each : form.coefs().entrySet()) {
            long one = each.getKey() instanceof Quantity.RemainderOfADividend remainder
                    ? value(remainder, at) : at.of(each.getKey());
            out = plus(out, times(each.getValue(), one));
        }
        return ((ExactAnswer.Held<BigInteger>) times(out, 2).floor()).value();
    }

    /** What {@code remainder} leaves at {@code at}; a dividend weighing half of the element is
     *  taken at the whole number below. */
    private static long value(Quantity.RemainderOfADividend remainder, Values at) {
        ExactRatio dividend = remainder.dividend().constant();
        for (Map.Entry<Quantity, ExactRatio> each : remainder.dividend().coefs().entrySet()) {
            dividend = plus(dividend, times(each.getValue(), at.of(each.getKey())));
        }
        long whole = ((ExactAnswer.Held<BigInteger>) dividend.floor()).value().longValueExact();
        return Math.floorMod(whole, remainder.divisor().longValueExact());
    }

    /** A remainder's dividend twice over, in whole numbers: a dividend weighs the element by a
     *  half at most. */
    private record Twice(long constant, Map<Quantity, Long> coefs, long divisor) {

        static Twice of(Quantity.RemainderOfADividend remainder) {
            Map<Quantity, Long> coefs = new LinkedHashMap<>();
            remainder.dividend().coefs().forEach((each, by) -> coefs.put(each, doubled(by)));
            return new Twice(doubled(remainder.dividend().constant()), coefs,
                    remainder.divisor().longValueExact());
        }

        private static long doubled(ExactRatio ratio) {
            return ((ExactAnswer.Held<BigInteger>) times(ratio, 2).floor()).value()
                    .longValueExact();
        }

        /** What the remainder leaves at {@code at}, the dividend taken at the whole number at or
         *  below it. */
        long leaves(Values at) {
            long sum = constant;
            for (Map.Entry<Quantity, Long> each : coefs.entrySet()) {
                sum += each.getValue() * at.of(each.getKey());
            }
            return Math.floorMod(Math.floorDiv(sum, 2), divisor);
        }
    }

    private static ExactRatio plus(ExactRatio one, ExactRatio other) {
        return one.plus(other).orNull();
    }

    private static ExactRatio times(ExactRatio one, long by) {
        return one.times(ExactRatio.of(by)).orNull();
    }

    /** The bindings {@code stated} weighs a value of — inside its remainders alone where
     *  {@code inRemainders}. */
    private static Set<Quantity> bindingsIn(Proposition stated, boolean inRemainders) {
        Set<Quantity> out = new HashSet<>();
        List<Quantity.RemainderOfADividend> remainders = new ArrayList<>();
        remaindersIn(stated, remainders);
        remainders.forEach(each -> each.dividend().coefs().keySet().forEach(atom -> {
            if (atom instanceof Quantity.OfABinding) {
                out.add(atom);
            }
        }));
        if (!inRemainders) {
            comparedIn(stated).forEach(form -> form.coefs().keySet().forEach(atom -> {
                if (atom instanceof Quantity.OfABinding) {
                    out.add(atom);
                }
            }));
        }
        return out;
    }

    private static List<LinearForm<Quantity>> comparedIn(Proposition stated) {
        return switch (stated) {
            case Proposition.All(var parts, var _) -> parts.stream()
                    .flatMap(each -> comparedIn(each).stream()).toList();
            case Proposition.Any(var parts, var _) -> parts.stream()
                    .flatMap(each -> comparedIn(each).stream()).toList();
            case Proposition.Compared(Relation.Affine(var form, var _), var _, var _) ->
                    List.of(form);
            default -> List.of();
        };
    }

    private static void remaindersIn(Proposition stated,
                                     List<Quantity.RemainderOfADividend> into) {
        switch (stated) {
            case Proposition.All(var parts, var _) -> parts.forEach(each -> remaindersIn(each, into));
            case Proposition.Any(var parts, var _) -> parts.forEach(each -> remaindersIn(each, into));
            case Proposition.Compared(Relation.Affine(var form, var _), var _, var _) ->
                    form.coefs().keySet().forEach(each -> {
                        if (each instanceof Quantity.RemainderOfADividend remainder) {
                            into.add(remainder);
                        }
                    });
            default -> { }
        }
    }
}
