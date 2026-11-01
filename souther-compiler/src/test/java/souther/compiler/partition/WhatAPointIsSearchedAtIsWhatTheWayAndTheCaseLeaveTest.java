package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.OnOneElement;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.meaning.WhyUnread;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.numeric.WholeNumberRuns;
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
 * The remainders a point is searched at, and whether a case can be asked of a row at some
 * element, are what working each of them out in full would give.
 *
 * <p>Three short ways in, each held against the long one. What the way to a point asks of a
 * remainder of the same form moved by a constant is turned back to the point's own remainder
 * ({@link Standing.OfARemainder#turnedBack}): a remainder is kept exactly where moving it by the
 * constant leaves one the way asks for. What a case leaves of a remainder, read once for the line
 * ({@link TheCaseALineDecidesIn}), is what reading the case leaves. And a case said to be one a row
 * can be asked at some element ({@link AStatementAtARow#askableAtSomeElement}), worked out part by
 * part without putting the element in, is one a row can be asked with the element put at any
 * value — the other way round need not hold, and is not asked.
 *
 * <p>Drawn at random from a fixed seed: runs of remainders inside and outside a divisor's, moved
 * either way; statements of remainders, of the element weighed itself, of another element no row
 * names, of truths and of parts nothing read, held together and as alternatives, denied.
 */
class WhatAPointIsSearchedAtIsWhatTheWayAndTheCaseLeaveTest {

    private static final NumericTerm D = new NumericTerm.ValueOf(TermPath.of("d"));
    private static final Quantity INPUT = new DecisionAtom.OfTheInput(D);
    private static final Quantity.OfABinding ELEMENT = element(0);
    private static final Quantity.OfABinding OTHER = element(1);
    private static final ValueName FLOOR_MOD = ValueName.Stdlib.operation("Int", "floorMod");

    @Test
    void aRemainderTheWayAsksForIsTurnedBackToThePointsOwn() {
        Random random = new Random(2937);
        for (int drawn = 0; drawn < 3000; drawn++) {
            int divisor = 1 + random.nextInt(12);
            WholeNumberRuns asked = WholeNumberRuns.NONE;
            for (int at = 0; at < 1 + random.nextInt(3); at++) {
                long from = random.nextInt(3 * divisor) - divisor;
                asked = asked.or(WholeNumberRuns.one(BigInteger.valueOf(from),
                        BigInteger.valueOf(from + random.nextInt(divisor + 1))));
            }
            long moved = random.nextInt(4 * divisor + 1) - 2L * divisor;
            WholeNumberRuns turned = Standing.OfARemainder.turnedBack(asked,
                    BigInteger.valueOf(moved), BigInteger.valueOf(divisor));
            for (long r = -divisor; r < 2L * divisor; r++) {
                boolean kept = r >= 0 && r < divisor
                        && asked.holds(BigInteger.valueOf(Math.floorMod(r + moved, divisor)));
                assertEquals(kept, turned.holds(BigInteger.valueOf(r)),
                        r + " by " + divisor + " moved " + moved + " into " + asked);
            }
        }
    }

    @Test
    void whatACaseLeavesOfARemainderIsReadOnceAsItIs() {
        Random random = new Random(2938);
        for (int drawn = 0; drawn < 300; drawn++) {
            Proposition decides = statement(random, 3, false);
            TheCaseALineDecidesIn kept = new TheCaseALineDecidesIn(decides);
            for (int asked = 0; asked < 6; asked++) {
                LinearForm<NumericTerm> dividend = new LinearForm<>(
                        ExactRatio.of(random.nextInt(5)), Map.of(D, ExactRatio.ONE));
                BigInteger divisor = BigInteger.valueOf(2 + random.nextInt(4));
                assertEquals(ResiduesAStatementLeaves.of(decides, dividend, divisor),
                        kept.remaindersOf(dividend, divisor),
                        decides.spelling() + " of " + dividend + " by " + divisor);
            }
        }
    }

    @Test
    void aCaseThatCanBeAskedAtSomeElementCanBeAskedAtEveryValueOfIt() {
        Random random = new Random(2939);
        int askable = 0;
        int not = 0;
        for (int drawn = 0; drawn < 3000; drawn++) {
            Proposition stated = statement(random, 3, true);
            Optional<Quantity.OfABinding> element = OnOneElement.theElementOf(stated);
            if (element.isEmpty()) {
                continue;
            }
            if (!AStatementAtARow.askableAtSomeElement(stated)) {
                not++;
                continue;
            }
            askable++;
            for (int value = -3; value <= 3; value++) {
                Proposition put = OnOneElement.at(stated, element.get(),
                        LinearForm.constant(ExactRatio.of(value)));
                int at = value;
                assertTrue(put == null || AStatementAtARow.askable(put),
                        () -> stated.spelling() + " put at " + at + ": " + put);
            }
        }
        assertTrue(askable > 0 && not > 0, askable + " askable, " + not + " not");
    }

    private static Quantity.OfABinding element(int slot) {
        return new Quantity.OfABinding(
                new BindingId(new BindingOwner.OfValue("demo", "f"), slot), List.of(), Type.INT,
                Optional.empty(), Optional.of(new Quantity.AWholeNumberInTurn(
                        LinearForm.constant(ExactRatio.ZERO),
                        new LinearForm<>(ExactRatio.ZERO, Map.of(D, ExactRatio.ONE)))));
    }

    /** A statement drawn at random; over the element and another where {@code bound}, over the
     *  input's number alone otherwise. */
    private static Proposition statement(Random random, int depth, boolean bound) {
        int kind = random.nextInt(depth == 0 ? 2 : 5);
        return switch (kind) {
            case 0 -> comparison(random, bound);
            // A truth of the input, or now and then a part nothing read, which no row is asked.
            case 1 -> random.nextInt(6) == 0
                    ? new Proposition.Unread(Optional.empty(), 0, new WhyUnread.NotArithmetic(),
                            false, random.nextBoolean())
                    : new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of("p")),
                            random.nextBoolean());
            default -> {
                List<Proposition> parts = new ArrayList<>();
                for (int at = 0; at < 2 + random.nextInt(2); at++) {
                    parts.add(statement(random, depth - 1, bound));
                }
                Proposition joined = kind == 2 ? Proposition.all(parts) : Proposition.any(parts);
                yield kind == 4 ? joined.denied() : joined;
            }
        };
    }

    private static Proposition comparison(Random random, boolean bound) {
        Map<Quantity, ExactRatio> dividend = new LinkedHashMap<>();
        dividend.put(INPUT, ExactRatio.ONE);
        if (bound) {
            dividend.put(random.nextInt(6) == 0 ? OTHER : ELEMENT,
                    ExactRatio.of(1 + random.nextInt(3)));
        }
        Map<Quantity, ExactRatio> coefs = new LinkedHashMap<>();
        if (bound && random.nextInt(8) == 0) {
            // Another element weighed itself, which no row names: no row can be asked it.
            coefs.put(OTHER, ExactRatio.ONE);
            coefs.put(INPUT, ExactRatio.ONE);
        } else {
            coefs.put(new Quantity.RemainderOfADividend(FLOOR_MOD,
                    new LinearForm<>(ExactRatio.of(random.nextInt(5)), dividend),
                    BigInteger.valueOf(2 + random.nextInt(4))), ExactRatio.ONE);
        }
        if (bound && random.nextInt(4) == 0) {
            coefs.put(ELEMENT, ExactRatio.of(random.nextInt(2) * 2 - 1));
        }
        Relation.OneWay<Quantity> one = Relation.OneWay.of(
                new LinearForm<>(ExactRatio.of(random.nextInt(5) - 2), coefs),
                new Rel[] {Rel.GE, Rel.GT, Rel.EQ}[random.nextInt(3)]);
        return new Proposition.Compared(new Relation.Affine(one.form(), one.proposition()),
                one.holds() == random.nextBoolean());
    }
}
