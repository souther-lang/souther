package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.types.BinOp;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What each way of comparing two values states, out of the two facts a claim holds.
 *
 * <p>Six ways to compare state three things between them, and which of the three is not read off
 * the operator: which class the value named is in says which side of the canonical order each of
 * the two goes on, and whether the comparison holds at the value says whether the statement is
 * denied. The two shapes read the second fact opposite ways, because an order does not hold at the
 * value it names and an equality does.
 *
 * <p><b>Against an algebra of its own.</b> What is fixed here is the derivation and not any
 * writing of it: the statements are read into three values this test declares, so a term and a
 * node that both got the derivation wrong the same way would not agree with what is written below.
 * The two writings are fixed where each of them is
 * ({@link TwoWritingsOfOneComparisonAreOneTermTest} and the readings of a condition).
 */
class WhatAComparisonStatesIsDerivedFromWhatItPlacedTest {

    /** What a canonical comparison of two sides states, as a value with nothing else in it. */
    private sealed interface Stated {

        record TheSameValue(String left, String right) implements Stated {}

        record Below(String left, String right) implements Stated {}

        record Denied(Stated of) implements Stated {}
    }

    private static final CanonicalComparison.Expression<String, Stated> AS_STATED =
            new CanonicalComparison.Expression<>() {

                @Override
                public Stated theSameValue(String left, String right) {
                    return new Stated.TheSameValue(left, right);
                }

                @Override
                public Stated below(String left, String right) {
                    return new Stated.Below(left, right);
                }

                @Override
                public Stated denied(Stated statement) {
                    return new Stated.Denied(statement);
                }
            };

    /** What each of the six states of a left side {@code l} and a right side {@code r}. */
    private static Map<BinOp, Stated> stated() {
        Map<BinOp, Stated> out = new LinkedHashMap<>();
        out.put(BinOp.EQ, new Stated.TheSameValue("l", "r"));
        out.put(BinOp.NE, new Stated.Denied(new Stated.TheSameValue("l", "r")));
        out.put(BinOp.LT, new Stated.Below("l", "r"));
        out.put(BinOp.GE, new Stated.Denied(new Stated.Below("l", "r")));
        out.put(BinOp.GT, new Stated.Below("r", "l"));
        out.put(BinOp.LE, new Stated.Denied(new Stated.Below("r", "l")));
        return out;
    }

    private static Stated canonical(BinOp op) {
        ComparisonClaim placed = (ComparisonClaim) ComparisonPlacement.of(op);
        return placed.canonical("l", "r").expressedAs(AS_STATED);
    }

    @Test
    void eachComparisonStatesOneOfTheThree() {
        Map<BinOp, Stated> derived = new LinkedHashMap<>();
        stated().keySet().forEach(op -> derived.put(op, canonical(op)));

        assertEquals(stated(), derived,
                "which of the three a comparison states, which side of it each value goes on and"
                        + " whether it is denied are one derivation from what the comparison"
                        + " placed, and a reader that pairs those facts for itself pairs them"
                        + " somewhere");
    }

    /**
     * A reader holding the two sides the other way round states the same thing, so long as it turns
     * the claim with them.
     *
     * <p>The one law that catches an order taken the wrong way round. The others hold of a
     * derivation that exchanged the sides of every order, or of none of them, because at the value
     * a comparison names both conventions agree — the difference shows only where one side really
     * is below the other.
     *
     * <p>Of the orders, because only they have sides to turn. An equality's two sides are one pair
     * and which of them was written first says nothing about it: that is answered where the
     * equality is written, and here it would be this test declaring it a second time.
     */
    @Test
    void aTurnedOrderStatesTheSameThingOfTheSidesTurnedWithIt() {
        stated().keySet().stream()
                .filter(op -> ComparisonPlacement.of(op) instanceof ComparisonClaim.Cut)
                .forEach(op -> {
                    ComparisonClaim placed = (ComparisonClaim) ComparisonPlacement.of(op);
                    assertEquals(placed.canonical("l", "r").expressedAs(AS_STATED),
                            placed.turned().canonical("r", "l").expressedAs(AS_STATED),
                            "turning the claim and the two sides together leaves the statement"
                                    + " alone: " + op);
                });
    }

    /** And a denied claim states the denial of what it stated. */
    @Test
    void aDeniedClaimStatesTheDenialOfWhatItStated() {
        stated().forEach((op, was) -> {
            ComparisonClaim placed = (ComparisonClaim) ComparisonPlacement.of(op);
            assertEquals(denial(was), placed.denied().canonical("l", "r").expressedAs(AS_STATED),
                    "what holds where a comparison does not is what it states, denied: " + op);
        });
    }

    private static Stated denial(Stated stated) {
        return stated instanceof Stated.Denied denied ? denied.of() : new Stated.Denied(stated);
    }
}
