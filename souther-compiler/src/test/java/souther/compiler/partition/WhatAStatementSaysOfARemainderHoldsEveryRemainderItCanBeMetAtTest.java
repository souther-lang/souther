package souther.compiler.partition;

import org.junit.jupiter.api.Test;

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
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The remainders a statement is read to hold at, of one form by one divisor, are every remainder
 * a row meeting it leaves, and exactly those where every part of it is a comparison of that
 * remainder.
 *
 * <p>The oracle is the statement worked out here at every pair of numbers over three turns of the
 * divisor, and at every assignment of the truths it asks of positions: those are parts nothing
 * reads a remainder of, and one truth asked twice is given one value at both. Statements are
 * drawn at random from a fixed seed: comparisons of the form's remainder moved by a constant,
 * weighed and held against a number, said to hold and not to; comparisons of a remainder by
 * another divisor and of another form, which the statement has to be read past; truths and
 * constants; held together and as alternatives, to a depth of three.
 *
 * <p>What is held of them is what a point is narrowed by: every remainder some row meeting the
 * statement leaves is among those read ({@link ResiduesAStatementLeaves}), so a point the read
 * remainders leave nothing of is one no row meeting the statement stands at; the read remainders
 * of two statements held together are among those of each; and a statement read whole is read
 * at exactly the remainders it holds at.
 */
class WhatAStatementSaysOfARemainderHoldsEveryRemainderItCanBeMetAtTest {

    private static final NumericTerm D = new NumericTerm.ValueOf(TermPath.of("d"));
    private static final NumericTerm S = new NumericTerm.ValueOf(TermPath.of("s"));
    private static final ValueName FLOOR_MOD = ValueName.Stdlib.operation("Int", "floorMod");
    private static final List<String> TRUTHS = List.of("p", "q");

    @Test
    void everyRemainderARowMeetingTheStatementLeavesIsRead() {
        Random random = new Random(2869);
        for (int divisor : new int[] {1, 4, 7, 12}) {
            for (int drawn = 0; drawn < 400; drawn++) {
                long moved = random.nextInt(divisor);
                Statement stated = statement(random, divisor, 3);
                WholeNumberRuns read = ResiduesAStatementLeaves.of(stated.proposition(),
                        form(moved), BigInteger.valueOf(divisor));
                Set<Long> met = metAt(stated, divisor, moved);
                String said = stated.proposition().spelling() + " over d - s + " + moved
                        + " by " + divisor;
                for (long remainder : met) {
                    assertTrue(read.holds(BigInteger.valueOf(remainder)),
                            () -> said + ": a row meeting it leaves " + remainder + ", read "
                                    + read);
                }
                if (stated.readWhole()) {
                    assertEquals(met, within(read, divisor), said);
                }
                // A point the read remainders leave nothing of: no row meeting it stands there.
                long point = random.nextInt(divisor);
                if (!read.holds(BigInteger.valueOf(point))) {
                    assertTrue(!met.contains(point), said + " at " + point);
                }
            }
        }
    }

    @Test
    void twoStatementsHeldTogetherAreReadAtNoMoreRemaindersThanEither() {
        Random random = new Random(2870);
        for (int divisor : new int[] {4, 7, 12}) {
            for (int drawn = 0; drawn < 300; drawn++) {
                long moved = random.nextInt(divisor);
                Proposition one = statement(random, divisor, 2).proposition();
                Proposition other = statement(random, divisor, 2).proposition();
                BigInteger by = BigInteger.valueOf(divisor);
                WholeNumberRuns both = ResiduesAStatementLeaves.of(
                        new Proposition.All(List.of(one, other)), form(moved), by);
                for (Proposition each : List.of(one, other)) {
                    WholeNumberRuns alone = ResiduesAStatementLeaves.of(each, form(moved), by);
                    for (long r = 0; r < divisor; r++) {
                        if (both.holds(BigInteger.valueOf(r))) {
                            long at = r;
                            assertTrue(alone.holds(BigInteger.valueOf(r)), () -> one.spelling()
                                    + " and " + other.spelling() + " at " + at);
                        }
                    }
                }
            }
        }
    }

    /** A remainder the first of a band leaves the statement nothing at, and another meets it:
     *  read at the other, and not at the first. */
    @Test
    void aBandIsReadAtTheRemaindersOfItThatMeetTheStatement() {
        Proposition stated = new Proposition.All(List.of(
                comparison(0, 1, Rel.GE, -2, true),
                comparison(3, 1, Rel.EQ, -5, false)));
        WholeNumberRuns read = ResiduesAStatementLeaves.of(stated, form(0), BigInteger.valueOf(7));
        Set<Long> met = new TreeSet<>();
        for (long r = 0; r < 7; r++) {
            if (r >= 2 && Math.floorMod(r + 3, 7) != 5) {
                met.add(r);
            }
        }
        assertEquals(met, within(read, 7));
        assertTrue(!read.holds(BigInteger.TWO), "two leaves d - s + 3 at five");
        assertTrue(read.holds(BigInteger.valueOf(3)), "three meets both");
    }

    /** A statement drawn at random, and whether every part of it is a comparison of the form's
     *  remainder by the divisor. */
    private record Statement(Proposition proposition, boolean readWhole) {}

    private static Statement statement(Random random, int divisor, int depth) {
        int kind = random.nextInt(depth == 0 ? 5 : 7);
        return switch (kind) {
            case 0, 1 -> new Statement(comparisonBy(random.nextInt(2 * divisor + 1) - divisor,
                    divisor,
                    new int[] {1, -1, 2}[random.nextInt(3)],
                    new Rel[] {Rel.GE, Rel.GT, Rel.EQ}[random.nextInt(3)],
                    random.nextInt(2 * divisor + 1) - divisor, random.nextBoolean()), true);
            case 2 -> new Statement(random.nextBoolean()
                    ? remainderOf(Map.of(D, ExactRatio.ONE, S, ExactRatio.of(-1)),
                            divisor + 1, random.nextInt(divisor + 1), random.nextBoolean())
                    : remainderOf(Map.of(D, ExactRatio.ONE), divisor, random.nextInt(divisor),
                            random.nextBoolean()), false);
            case 3 -> new Statement(new Proposition.Truth(new DecisionSubject.AnInput(
                    TermPath.of(TRUTHS.get(random.nextInt(TRUTHS.size())))),
                    random.nextBoolean()), false);
            case 4 -> new Statement(new Proposition.Always(random.nextBoolean()), true);
            default -> {
                List<Proposition> parts = new ArrayList<>();
                boolean whole = true;
                for (int at = 0; at < 2 + random.nextInt(2); at++) {
                    Statement part = statement(random, divisor, depth - 1);
                    parts.add(part.proposition());
                    whole &= part.readWhole();
                }
                yield new Statement(kind == 5 ? new Proposition.All(parts)
                        : new Proposition.Any(parts), whole);
            }
        };
    }

    /** {@code weight·floorMod(d - s + shift, 7) + constant rel 0}, held as {@code holds}. */
    private static Proposition comparison(long shift, int weight, Rel rel, long constant,
                                          boolean holds) {
        return comparisonBy(shift, 7, weight, rel, constant, holds);
    }

    private static Proposition comparisonBy(long shift, int divisor, int weight, Rel rel,
                                            long constant, boolean holds) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(D, ExactRatio.ONE);
        coefs.put(S, ExactRatio.of(-1));
        Quantity remainder = Quantity.RemainderOfADividend.ofTheInput(FLOOR_MOD,
                new LinearForm<>(ExactRatio.of(shift), coefs), BigInteger.valueOf(divisor));
        return compared(new LinearForm<>(ExactRatio.of(constant),
                Map.of(remainder, ExactRatio.of(weight))), rel, holds);
    }

    /** {@code form rel 0} held as {@code holds}, written facing the way a relation is. */
    private static Proposition compared(LinearForm<Quantity> form, Rel rel, boolean holds) {
        Relation.OneWay<Quantity> one = Relation.OneWay.of(form, rel);
        return new Proposition.Compared(new Relation.Affine(one.form(), one.proposition()),
                holds == one.holds());
    }

    /** {@code floorMod(coefs, divisor) >= level}, as {@code holds}. */
    private static Proposition remainderOf(Map<NumericTerm, ExactRatio> coefs, int divisor,
                                           long level, boolean holds) {
        Quantity remainder = Quantity.RemainderOfADividend.ofTheInput(FLOOR_MOD,
                new LinearForm<>(ExactRatio.ZERO, coefs), BigInteger.valueOf(divisor));
        return compared(new LinearForm<>(ExactRatio.of(-level), Map.of(remainder, ExactRatio.ONE)),
                Rel.GE, holds);
    }

    private static LinearForm<NumericTerm> form(long moved) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(D, ExactRatio.ONE);
        coefs.put(S, ExactRatio.of(-1));
        return new LinearForm<>(ExactRatio.of(moved), coefs);
    }

    /** The remainders of {@code d - s + moved} by {@code divisor} at which some pair of numbers
     *  over three turns of it, and some assignment of the truths, meets {@code stated}. */
    private static Set<Long> metAt(Statement stated, int divisor, long moved) {
        Set<Long> out = new TreeSet<>();
        for (long d = 0; d < 3L * divisor; d++) {
            for (long s = 0; s < 3L * divisor; s++) {
                for (int truths = 0; truths < 1 << TRUTHS.size(); truths++) {
                    if (holds(stated.proposition(), d, s, truths)) {
                        out.add(Math.floorMod(d - s + moved, (long) divisor));
                    }
                }
            }
        }
        return out;
    }

    private static boolean holds(Proposition stated, long d, long s, int truths) {
        return switch (stated) {
            case Proposition.Always(boolean holds) -> holds;
            case Proposition.All(var parts, var _) ->
                    parts.stream().allMatch(each -> holds(each, d, s, truths));
            case Proposition.Any(var parts, var _) ->
                    parts.stream().anyMatch(each -> holds(each, d, s, truths));
            case Proposition.Truth(DecisionSubject.AnInput(TermPath at), boolean holds, var _) ->
                    (((truths >> TRUTHS.indexOf(at.toString())) & 1) == 1) == holds;
            case Proposition.Compared(Relation.Affine affine, boolean holds, var _) -> {
                BigInteger sum = BigInteger.valueOf(whole(affine.form().constant()));
                for (Map.Entry<Quantity, ExactRatio> each : affine.form().coefs().entrySet()) {
                    Quantity.RemainderOfADividend remainder =
                            (Quantity.RemainderOfADividend) each.getKey();
                    long value = 0;
                    for (Map.Entry<Quantity, ExactRatio> term
                            : remainder.dividend().coefs().entrySet()) {
                        long at = ((DecisionAtom.OfTheInput) term.getKey()).term().equals(D) ? d
                                : s;
                        value += whole(term.getValue()) * at;
                    }
                    value += whole(remainder.dividend().constant());
                    long left = Math.floorMod(value, remainder.divisor().longValueExact());
                    sum = sum.add(BigInteger.valueOf(whole(each.getValue()) * left));
                }
                yield affine.proposition().holds(sum.signum()) == holds;
            }
            default -> throw new AssertionError("no such statement is drawn: " + stated);
        };
    }

    private static long whole(ExactRatio ratio) {
        return ((ExactAnswer.Held<BigInteger>) ratio.floor()).value().longValueExact();
    }

    private static Set<Long> within(WholeNumberRuns read, int divisor) {
        Set<Long> out = new TreeSet<>();
        for (long r = 0; r < divisor; r++) {
            if (read.holds(BigInteger.valueOf(r))) {
                out.add(r);
            }
        }
        return out;
    }
}
