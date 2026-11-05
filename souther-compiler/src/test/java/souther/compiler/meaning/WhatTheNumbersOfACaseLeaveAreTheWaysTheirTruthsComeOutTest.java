package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.types.ValueName;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the numbers of a case leave is how many ways the truths of its parts come out together,
 * found by trying every value: of one number against orderings of it, every stretch and point
 * between the constants; of remainders of one dividend, every remainder.
 */
class WhatTheNumbersOfACaseLeaveAreTheWaysTheirTruthsComeOutTest {

    private static final Quantity NUMBER =
            new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(TermPath.of("x")));
    private static final ValueName FLOOR_MOD = ValueName.Stdlib.operation("Int", "floorMod");
    private static final int DIVISOR = 7;
    private static final Rel[] ORDERINGS = {Rel.GE, Rel.GT, Rel.LE, Rel.LT};

    private static Proposition.Compared compared(Quantity of, int constant, Rel rel) {
        Relation.OneWay<Quantity> one = Relation.OneWay.of(
                new LinearForm<>(ExactRatio.of(constant), new LinkedHashMap<>(Map.of(of,
                        ExactRatio.ONE))), rel);
        return new Proposition.Compared(new Relation.Affine(one.form(), one.proposition()),
                one.holds());
    }

    private static Quantity remainderMovedBy(int by) {
        return new Quantity.RemainderOfADividend(FLOOR_MOD,
                new LinearForm<>(ExactRatio.of(by), Map.of(NUMBER, ExactRatio.ONE)),
                BigInteger.valueOf(DIVISOR));
    }

    private static boolean holds(Proposition.Compared comparison, ExactRatio value) {
        Relation.Affine affine = (Relation.Affine) comparison.relation();
        ExactRatio left = value.plus(affine.form().constant()).orNull();
        return affine.proposition().holds(left.signum()) == comparison.holds();
    }

    /** Each part a case of its own, so a case is taken apart on every one of them. */
    private static DecidingCase.Cases eachOf(List<Proposition.Compared> parts) {
        return new DecidingCase.Cases.EachOf(parts.stream()
                .<DecidingCase.Cases>map(DecidingCase.Cases.One::new).toList());
    }

    @Test
    void orderingsOfOneNumberComeOutAsManyWaysAsTheStretchesAndPointsBetweenThem() {
        Random random = new Random(3042);
        for (int trial = 0; trial < 300; trial++) {
            Map<List<Object>, Proposition.Compared> parts = new LinkedHashMap<>();
            int many = 2 + random.nextInt(6);
            while (parts.size() < many) {
                Rel rel = ORDERINGS[random.nextInt(ORDERINGS.length)];
                Proposition.Compared one = compared(NUMBER, -random.nextInt(9) + 4, rel);
                // One part however it is turned: a comparison and its denial are one.
                parts.putIfAbsent(List.of(one.relation()), one);
            }
            List<Proposition.Compared> each = List.copyOf(parts.values());
            Set<List<Boolean>> ways = new HashSet<>();
            for (int doubled = -20; doubled <= 20; doubled++) {
                ExactRatio value = ExactRatio.of(BigInteger.valueOf(doubled), BigInteger.TWO);
                ways.add(each.stream().map(one -> holds(one, value)).toList());
            }
            List<CaseExpansion.Diagnosis> said = WhatTheNumbersOfACaseLeave.of(eachOf(each));
            CaseExpansion.OrderedBoundaries ordered = said.stream()
                    .filter(CaseExpansion.OrderedBoundaries.class::isInstance)
                    .map(CaseExpansion.OrderedBoundaries.class::cast).findFirst()
                    .orElseThrow(() -> new AssertionError("orderings of one number: " + each));
            assertEquals(each.size(), ordered.comparisons(), each::toString);
            assertEquals(ways.size(), ordered.waysAtMost(),
                    () -> "every stretch and point the constants leave: " + each);
        }
    }

    @Test
    void remaindersOfOneDividendComeOutAsManyWaysAsTheRemaindersTellThemApart() {
        Random random = new Random(7);
        for (int trial = 0; trial < 300; trial++) {
            Map<List<Object>, Proposition.Compared> parts = new LinkedHashMap<>();
            int many = 2 + random.nextInt(6);
            while (parts.size() < many) {
                Rel rel = ORDERINGS[random.nextInt(ORDERINGS.length)];
                Proposition.Compared one = compared(remainderMovedBy(random.nextInt(11)),
                        -random.nextInt(DIVISOR), rel);
                parts.putIfAbsent(List.of(one.relation()), one);
            }
            List<Proposition.Compared> each = List.copyOf(parts.values());
            Set<List<Boolean>> ways = new HashSet<>();
            for (int residue = 0; residue < DIVISOR; residue++) {
                List<Boolean> truths = new ArrayList<>();
                for (Proposition.Compared one : each) {
                    Quantity.RemainderOfADividend remainder = (Quantity.RemainderOfADividend)
                            ((Relation.Affine) one.relation()).form().coefs().keySet()
                                    .iterator().next();
                    int moved = Math.floorMod(residue
                            + remainder.dividend().constant().floor().orNull().intValueExact(),
                            DIVISOR);
                    truths.add(holds(one, ExactRatio.of(moved)));
                }
                ways.add(truths);
            }
            List<CaseExpansion.Diagnosis> said = WhatTheNumbersOfACaseLeave.of(eachOf(each));
            CaseExpansion.CorrelatedRemainders correlated = said.stream()
                    .filter(CaseExpansion.CorrelatedRemainders.class::isInstance)
                    .map(CaseExpansion.CorrelatedRemainders.class::cast).findFirst()
                    .orElseThrow(() -> new AssertionError("remainders of one dividend: " + each));
            assertEquals(each.size(), correlated.comparisons(), each::toString);
            assertEquals(ways.size(), correlated.ways(),
                    () -> "every remainder tried: " + each);
            assertTrue(correlated.ways() <= DIVISOR);
        }
    }

    @Test
    void anEqualityIsNoBoundaryAndOneComparisonIsNoDiagnosis() {
        assertEquals(List.of(), WhatTheNumbersOfACaseLeave.of(eachOf(List.of(
                compared(NUMBER, -1, Rel.EQ), compared(NUMBER, -2, Rel.EQ),
                compared(NUMBER, -3, Rel.GE)))),
                "equalities are left out, and one ordering is nothing tied to another");
    }
}
