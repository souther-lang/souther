package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.numeric.WholeNumberRuns;
import souther.compiler.types.ValueName;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a point at a remainder of {@code d - s} by seven says every row there makes of a statement
 * ({@link Standing#makesOf}) is what every such row does: where it says the statement holds, it
 * holds on each, and where it says it fails, it holds on none.
 *
 * <p>The oracle is the statement worked out at every pair of numbers over three turns of the
 * divisor leaving the remainder, under each truth of an input flag. A statement read where an
 * operation answers ({@link Proposition.WhereItAnswers}) holds only where the flag it is read
 * under does, and its denial likewise: at a remainder its denial is met nowhere, it is still not
 * held on the rows the flag fails on, and is said nothing of.
 */
class WhatARowAtARemainderMakesOfAStatementHoldsOfEveryRowThereTest {

    private static final NumericTerm D = new NumericTerm.ValueOf(TermPath.of("d"));
    private static final NumericTerm S = new NumericTerm.ValueOf(TermPath.of("s"));
    private static final ValueName FLOOR_MOD = ValueName.Stdlib.operation("Int", "floorMod");
    private static final int DIVISOR = 7;
    private static final Proposition FLAG =
            new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of("flag")), true);

    @Test
    void whatEveryPointSaysOfAStatementEveryRowAtItMakesOfIt() {
        List<Proposition> statements = statements();
        for (int r = 0; r < DIVISOR; r++) {
            for (Standing point : pointsAt(r)) {
                for (Proposition stated : statements) {
                    Optional<Boolean> made = point.makesOf(stated);
                    if (made.isEmpty()) {
                        continue;
                    }
                    int remainder = r;
                    for (long d = 0; d < 3L * DIVISOR; d++) {
                        for (long s = 0; s < 3L * DIVISOR; s++) {
                            if (Math.floorMod(d - s, DIVISOR) != remainder) {
                                continue;
                            }
                            for (boolean flag : new boolean[] {true, false}) {
                                long dd = d;
                                long ss = s;
                                assertEquals(made.get(), holds(stated, d, s, flag),
                                        () -> point + " says " + made.get() + " of "
                                                + stated.spelling() + " at d=" + dd + " s=" + ss
                                                + " flag=" + flag);
                            }
                        }
                    }
                }
            }
        }
    }

    /** At the remainder a comparison is of, the comparison is said to hold: the check above is
     *  asked of some truth said, and not only of points that say nothing. */
    @Test
    void aComparisonOfTheRemainderIsSaidToHoldAtIt() {
        Proposition atNought = comparison(Rel.EQ, 0, true);
        Proposition readUnderTheFlag = new Proposition.WhereItAnswers(FLAG, atNought);
        for (Standing point : pointsAt(0)) {
            assertEquals(Optional.of(true), point.makesOf(atNought), point.toString());
            assertEquals(Optional.of(false), point.makesOf(readUnderTheFlag.denied()),
                    point.toString());
            assertTrue(point.makesOf(readUnderTheFlag).isEmpty(), point.toString());
        }
    }

    private static List<Proposition> statements() {
        List<Proposition> out = new ArrayList<>();
        for (int level = 0; level < DIVISOR; level++) {
            for (Rel rel : List.of(Rel.EQ, Rel.GE)) {
                for (boolean holds : new boolean[] {true, false}) {
                    Proposition compared = comparison(rel, level, holds);
                    out.add(compared);
                    Proposition read = new Proposition.WhereItAnswers(FLAG, compared);
                    out.add(read);
                    out.add(read.denied());
                }
            }
        }
        out.add(FLAG);
        out.add(FLAG.denied());
        return out;
    }

    /** Points at {@code r} alone: of the remainder, and of the remainder with a form added. */
    private static List<Standing> pointsAt(int r) {
        Map<NumericTerm, Carrier> on = new LinkedHashMap<>();
        on.put(D, Carrier.WHOLE);
        on.put(S, Carrier.WHOLE);
        BigInteger divisor = BigInteger.valueOf(DIVISOR);
        WholeNumberRuns at = WholeNumberRuns.one(BigInteger.valueOf(r), BigInteger.valueOf(r));
        Criterion where = new Criterion.AtTheLevel(Level.OfTheQuantity.of(0));
        LevelSpace levels = LevelSpace.steppingBy(ExactRatio.ONE);
        NumericTerm added = new NumericTerm.ValueOf(TermPath.of("y"));
        return List.of(
                new Standing.OfARemainder(form(), on, levels, divisor, at, where),
                new Standing.OfARemainderAndAForm(form(), on, divisor, at,
                        new LinearForm<>(ExactRatio.ZERO, Map.of(added, ExactRatio.ONE)),
                        Map.of(added, Carrier.WHOLE), levels, where));
    }

    /** {@code floorMod(d - s, 7) rel level}, held as {@code holds}. */
    private static Proposition comparison(Rel rel, long level, boolean holds) {
        Quantity remainder = Quantity.RemainderOfADividend.ofTheInput(FLOOR_MOD, form(),
                BigInteger.valueOf(DIVISOR));
        Relation.OneWay<Quantity> one = Relation.OneWay.of(
                new LinearForm<>(ExactRatio.of(-level), Map.of(remainder, ExactRatio.ONE)), rel);
        return new Proposition.Compared(new Relation.Affine(one.form(), one.proposition()),
                holds == one.holds());
    }

    private static LinearForm<NumericTerm> form() {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(D, ExactRatio.ONE);
        coefs.put(S, ExactRatio.of(-1));
        return new LinearForm<>(ExactRatio.ZERO, coefs);
    }

    /** Whether {@code stated} holds at the row: one read where an operation answers holds where
     *  that answers and the statement read holds. */
    private static boolean holds(Proposition stated, long d, long s, boolean flag) {
        return switch (stated) {
            case Proposition.Truth(DecisionSubject.AnInput _, boolean holds, var _) ->
                    flag == holds;
            case Proposition.WhereItAnswers(var answers, var states, var _) ->
                    holds(answers, d, s, flag) && holds(states, d, s, flag);
            case Proposition.Compared(Relation.Affine affine, boolean holds, var _, var _) -> {
                long sum = whole(affine.form().constant());
                for (Map.Entry<Quantity, ExactRatio> each : affine.form().coefs().entrySet()) {
                    Quantity.RemainderOfADividend remainder =
                            (Quantity.RemainderOfADividend) each.getKey();
                    long value = whole(remainder.dividend().constant());
                    for (Map.Entry<Quantity, ExactRatio> term
                            : remainder.dividend().coefs().entrySet()) {
                        long at = ((DecisionAtom.OfTheInput) term.getKey()).term().equals(D) ? d
                                : s;
                        value += whole(term.getValue()) * at;
                    }
                    sum += whole(each.getValue())
                            * Math.floorMod(value, remainder.divisor().longValueExact());
                }
                yield affine.proposition().holds(Long.signum(sum)) == holds;
            }
            default -> throw new AssertionError("no such statement is made: " + stated);
        };
    }

    private static long whole(ExactRatio ratio) {
        return ((ExactAnswer.Held<BigInteger>) ratio.floor()).value().longValueExact();
    }
}
