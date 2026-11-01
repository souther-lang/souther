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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a statement over the element of {@code List.rangeInclusive(0, y)} comes to on the elements
 * the list starts with stands for what it comes to on every element of it.
 *
 * <p>Two claims, each held against the statement worked out here at every element and every value
 * of the input's numbers. A statement said to come out alike on elements some number apart
 * ({@link OnOneElement#comesOutAlikeApart}) does, wherever the list holds both. And some element
 * the list holds meets the statement exactly where one of the readings on its first elements
 * ({@link TheWholeNumbersAListStartsWith#of}) holds at a row whose list holds an element coming
 * round to it — or where the statement holds on one of those first elements whatever the row is,
 * which is no reading of its own.
 *
 * <p>Drawn at random from a fixed seed: comparisons of remainders of the element and a number of
 * the input by divisors of their own, the element weighed by whole numbers either side of nought,
 * held together and as alternatives, denied; and, beside them, statements no reading of this kind
 * holds — the element outside a remainder — so that both answers are asked.
 */
class TheFirstElementsOfAListStandForEveryElementOfItTest {

    private static final NumericTerm X = new NumericTerm.ValueOf(TermPath.of("x"));
    private static final NumericTerm Y = new NumericTerm.ValueOf(TermPath.of("y"));
    private static final Quantity INPUT = new DecisionAtom.OfTheInput(X);
    private static final Quantity END = new DecisionAtom.OfTheInput(Y);
    private static final Quantity.OfABinding ELEMENT = new Quantity.OfABinding(
            new BindingId(new BindingOwner.OfValue("demo", "f"), 0), List.of(), Type.INT,
            Optional.empty(), Optional.of(new Quantity.AWholeNumberInTurn(
                    LinearForm.constant(ExactRatio.ZERO),
                    new LinearForm<>(ExactRatio.ZERO, Map.of(Y, ExactRatio.ONE)))));
    private static final ValueName FLOOR_MOD = ValueName.Stdlib.operation("Int", "floorMod");

    @Test
    void aStatementSaidToComeOutAlikeApartDoesWhereverItsListHoldsBoth() {
        Random random = new Random(2937);
        int alike = 0;
        int not = 0;
        for (int drawn = 0; drawn < 1500; drawn++) {
            Proposition said = statement(random, 3);
            List<Proposition> parts = new ArrayList<>(OnOneElement.heldByItsList(ELEMENT));
            parts.add(said);
            Proposition stated = Proposition.all(parts);
            long apart = 1L + random.nextInt(12);
            if (!OnOneElement.comesOutAlikeApart(stated, ELEMENT, BigInteger.valueOf(apart))) {
                not++;
                continue;
            }
            alike++;
            long y = 3 * apart;
            for (long n = 0; n + apart <= y; n++) {
                for (long x = -3; x <= 3; x++) {
                    long at = n;
                    long of = x;
                    assertEquals(holds(stated, n, x, y), holds(stated, n + apart, x, y),
                            () -> stated.spelling() + " at " + at + " and " + (at + apart)
                                    + " with x " + of);
                }
            }
        }
        assertTrue(alike > 0 && not > 0, alike + " alike, " + not + " not shown");
    }

    @Test
    void someElementMeetsTheStatementExactlyWhereAReadingOnTheFirstOnesHolds() {
        Random random = new Random(2938);
        int read = 0;
        int refused = 0;
        for (int drawn = 0; drawn < 600; drawn++) {
            Proposition stated = statement(random, 3);
            if (!(TheWholeNumbersAListStartsWith.of(stated)
                    instanceof TheWholeNumbersAListStartsWith.Read.OnEach(var each))) {
                refused++;
                continue;
            }
            read++;
            long every = TheElementComesRound.in(stated)
                    .or(() -> TheElementComesRound.inItsRemainders(stated)).orElseThrow()
                    .every().longValueExact();
            // Lists ending before the first element, inside the first turn and just past it: past
            // a turn, every element comes round to one of the first ones.
            for (long y = -1; y <= every + 1; y++) {
                for (long x = -2; x <= 2; x++) {
                    boolean some = false;
                    for (long n = 0; n <= y; n++) {
                        some |= holds(stated, n, x, y);
                    }
                    boolean readSo = false;
                    // What a reading keeps of the element is read at the element coming round to
                    // the one it is read on.
                    for (TheWholeNumbersAListStartsWith.OnOne one : each) {
                        for (long n = 0; n <= y; n++) {
                            readSo |= holds(one.holding(), n, x, y)
                                    && holds(one.stated(), n, x, y);
                        }
                    }
                    // An element on which the statement holds whatever the row is draws no
                    // reading, and is one of the first ones the list holds.
                    for (long j = 0; j < every && j <= y; j++) {
                        boolean everywhere = true;
                        for (long other = -2; other <= 2; other++) {
                            everywhere &= holds(stated, j, other, y);
                        }
                        readSo |= everywhere;
                    }
                    long end = y;
                    long of = x;
                    assertEquals(some, readSo, () -> stated.spelling() + " over 0.." + end
                            + " with x " + of + ": " + each);
                }
            }
        }
        assertTrue(read > 0 && refused > 0, read + " read, " + refused + " refused");
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

    /** A comparison of a remainder of the element and the number; now and then the element
     *  weighed itself as well. */
    private static Proposition comparison(Random random) {
        Map<Quantity, ExactRatio> dividend = new LinkedHashMap<>();
        dividend.put(ELEMENT, ExactRatio.of(random.nextInt(7) - 3));
        dividend.put(INPUT, ExactRatio.of(random.nextInt(3) - 1));
        dividend.values().removeIf(each -> each.signum() == 0);
        if (dividend.isEmpty()) {
            dividend.put(ELEMENT, ExactRatio.ONE);
        }
        Map<Quantity, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(new Quantity.RemainderOfADividend(FLOOR_MOD,
                new LinearForm<>(ExactRatio.of(random.nextInt(9) - 4), dividend),
                BigInteger.valueOf(1 + random.nextInt(4))), ExactRatio.of(1 + random.nextInt(2)));
        if (random.nextInt(10) == 0) {
            coefs.put(ELEMENT, ExactRatio.ONE);
        }
        Relation.OneWay<Quantity> one = Relation.OneWay.of(
                new LinearForm<>(ExactRatio.of(random.nextInt(7) - 3), coefs),
                new Rel[] {Rel.GE, Rel.GT, Rel.EQ}[random.nextInt(3)]);
        return new Proposition.Compared(new Relation.Affine(one.form(), one.proposition()),
                one.holds() == random.nextBoolean());
    }

    /** Whether {@code stated} holds with the element at {@code n}, the number at {@code x} and
     *  the list's end at {@code y}. */
    private static boolean holds(Proposition stated, long n, long x, long y) {
        return switch (stated) {
            case Proposition.Always(boolean holds) -> holds;
            case Proposition.All(var parts, var _) ->
                    parts.stream().allMatch(each -> holds(each, n, x, y));
            case Proposition.Any(var parts, var _) ->
                    parts.stream().anyMatch(each -> holds(each, n, x, y));
            case Proposition.Compared(Relation.Affine affine, boolean holds, var _) ->
                    affine.proposition().holds(Long.signum(sum(affine.form(), n, x, y))) == holds;
            default -> throw new AssertionError("no such statement is drawn: " + stated);
        };
    }

    private static long sum(LinearForm<Quantity> form, long n, long x, long y) {
        long out = whole(form.constant());
        for (Map.Entry<Quantity, ExactRatio> each : form.coefs().entrySet()) {
            long at = each.getKey() instanceof Quantity.RemainderOfADividend remainder
                    ? Math.floorMod(sum(remainder.dividend(), n, x, y),
                            remainder.divisor().longValueExact())
                    : each.getKey().equals(ELEMENT) ? n
                    : each.getKey().equals(INPUT) ? x
                    : each.getKey().equals(END) ? y
                    : unknown(each.getKey());
            out += whole(each.getValue()) * at;
        }
        return out;
    }

    private static long unknown(Quantity each) {
        throw new AssertionError("no such number is drawn: " + each);
    }

    private static long whole(ExactRatio ratio) {
        return ((ExactAnswer.Held<BigInteger>) ratio.floor()).value().longValueExact();
    }
}
