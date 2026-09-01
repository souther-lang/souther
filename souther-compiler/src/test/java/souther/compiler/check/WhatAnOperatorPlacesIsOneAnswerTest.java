package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.numeric.NumericDomain.Rel;
import souther.compiler.numeric.Towards;
import souther.compiler.types.BinOp;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * The algebra of what an operator places, which is what lets a reader stop holding the operator.
 *
 * <p>Each law is what some reading rests on. That the classification and {@link BinOp#compares}
 * agree is what makes a claim the evidence that an operator compares. That turning a statement
 * round twice is the statement is what lets a reading turn one round wherever it meets it. That
 * classifying the operator a swap would have been written with is the same as turning the
 * classification round is what lets a reader swap the sides without an operator table of its own,
 * and the same holds of a denial — a rule met under a negation states the comparison that holds
 * where it does not, and asking which operator that would have been is a second table.
 *
 * <p>And the two facts a cut holds are put together in one place, so the side a rule is satisfied
 * on is one answer however many readings want it. Turning a comparison round moves it and denying
 * one moves it, which is the whole of what the two operations do to a line.
 */
class WhatAnOperatorPlacesIsOneAnswerTest {

    /** The operator each one states when its two operands change places. Written out here and
     *  nowhere in the compiler: what a reading does with a swap is turn the claim round, and this
     *  is the table that says the two are one. */
    private static final Map<BinOp, BinOp> SWAPPED = swapped();

    /** The operator each one states the failure of. Written out here and nowhere in the compiler:
     *  what a reading does with a negation is deny the claim, and this is the table that says the
     *  two are one. */
    private static final Map<BinOp, BinOp> DENIED = denied();

    /** Which side of its own line each order is true on. The four cases of the one derivation from
     *  the two facts a cut holds. */
    private static final Map<BinOp, Towards> SATISFIED_ON = satisfiedOn();

    /** The relation each comparison states of its two sides. Written out here and nowhere in the
     *  compiler: what a reader wanting the numeric words does is ask the claim, and this is the
     *  table that says which answer that is. */
    private static final Map<BinOp, Rel> STATED = stated();

    private static Map<BinOp, Rel> stated() {
        Map<BinOp, Rel> relations = new LinkedHashMap<>();
        relations.put(BinOp.LT, Rel.LT);
        relations.put(BinOp.LE, Rel.LE);
        relations.put(BinOp.GT, Rel.GT);
        relations.put(BinOp.GE, Rel.GE);
        relations.put(BinOp.EQ, Rel.EQ);
        relations.put(BinOp.NE, Rel.NE);
        return relations;
    }

    private static Map<BinOp, BinOp> swapped() {
        Map<BinOp, BinOp> pairs = new LinkedHashMap<>();
        pairs.put(BinOp.LT, BinOp.GT);
        pairs.put(BinOp.GT, BinOp.LT);
        pairs.put(BinOp.LE, BinOp.GE);
        pairs.put(BinOp.GE, BinOp.LE);
        pairs.put(BinOp.EQ, BinOp.EQ);
        pairs.put(BinOp.NE, BinOp.NE);
        return pairs;
    }

    private static Map<BinOp, BinOp> denied() {
        Map<BinOp, BinOp> pairs = new LinkedHashMap<>();
        pairs.put(BinOp.LT, BinOp.GE);
        pairs.put(BinOp.GE, BinOp.LT);
        pairs.put(BinOp.LE, BinOp.GT);
        pairs.put(BinOp.GT, BinOp.LE);
        pairs.put(BinOp.EQ, BinOp.NE);
        pairs.put(BinOp.NE, BinOp.EQ);
        return pairs;
    }

    private static Map<BinOp, Towards> satisfiedOn() {
        Map<BinOp, Towards> sides = new LinkedHashMap<>();
        sides.put(BinOp.LT, Towards.BELOW);
        sides.put(BinOp.LE, Towards.BELOW);
        sides.put(BinOp.GT, Towards.ABOVE);
        sides.put(BinOp.GE, Towards.ABOVE);
        return sides;
    }

    /** What an operator places is a claim exactly where the operator compares. Two spellings of one
     *  membership drift, and an operator added to the language would land in them differently. */
    @Test
    void whatPlacesSomethingIsWhatCompares() {
        Map<BinOp, Boolean> places = new LinkedHashMap<>();
        Map<BinOp, Boolean> compares = new LinkedHashMap<>();
        for (BinOp op : BinOp.values()) {
            places.put(op, ComparisonPlacement.of(op) instanceof ComparisonClaim);
            compares.put(op, op.compares());
        }
        assertEquals(compares, places,
                "what an operator places and whether it compares are one question");
    }

    /** Turning a statement round twice is the statement. Asked of every operator and not of the
     *  comparisons alone, because it is the wide answer a reader of any binary turns round. */
    @Test
    void turningAPlacementRoundTwiceLeavesIt() {
        for (BinOp op : BinOp.values()) {
            ComparisonPlacement placed = ComparisonPlacement.of(op);
            assertEquals(placed, placed.turned().turned(),
                    () -> "turning " + op + " round twice states what it stated");
        }
    }

    /**
     * Reading the swapped operator and turning the reading round come to the same claim.
     *
     * <p>What a reader of a comparison written the other way round rests on. Where the two part, a
     * reading that swaps the sides and turns the claim round says something the source did not, and
     * the only way to notice is to write the operator table again beside it.
     */
    @Test
    void swappingTheSidesIsTurningWhatWasPlaced() {
        for (Map.Entry<BinOp, BinOp> each : SWAPPED.entrySet()) {
            assertEquals(ComparisonPlacement.of(each.getValue()),
                    ComparisonPlacement.of(each.getKey()).turned(),
                    () -> "what " + each.getKey() + " places, turned round, is what "
                            + each.getValue() + " places");
        }
    }

    /** An operator that places nothing has nothing to turn round, which is what lets a reading of
     *  any binary turn one round before it knows whether it is a comparison. */
    @Test
    void anOperatorThatPlacesNothingTurnsIntoItself() {
        for (BinOp op : BinOp.values()) {
            if (op.compares()) {
                continue;
            }
            ComparisonPlacement placed = ComparisonPlacement.of(op);
            assertEquals(placed, placed.turned(),
                    () -> op + " places nothing, and nothing turned round is nothing");
        }
    }

    /**
     * Reading the operator that holds where one does not and denying the reading come to the same
     * claim.
     *
     * <p>What a reading meeting a rule under a negation rests on. Where the two part, a reading
     * that denies the claim states a rule the source did not, and the way it was noticed before was
     * to write the operator table again beside it.
     */
    @Test
    void denyingAComparisonIsReadingTheOneThatHoldsWhereItDoesNot() {
        for (Map.Entry<BinOp, BinOp> each : DENIED.entrySet()) {
            assertEquals(ComparisonPlacement.of(each.getValue()),
                    claim(each.getKey()).denied(),
                    () -> "what " + each.getKey() + " places, denied, is what "
                            + each.getValue() + " places");
        }
    }

    /** Denying a claim twice is the claim, which is what lets a reading deny one wherever it meets
     *  a negation rather than counting how many it is under. */
    @Test
    void denyingAClaimTwiceLeavesIt() {
        for (BinOp op : DENIED.keySet()) {
            assertEquals(claim(op), claim(op).denied().denied(),
                    () -> "denying " + op + " twice states what it stated");
        }
    }

    /** Turning a claim round and denying it are done in either order, which is what lets a reading
     *  do them as it meets them rather than in an order it has to keep. */
    @Test
    void turningAndDenyingAreDoneInEitherOrder() {
        for (BinOp op : DENIED.keySet()) {
            assertEquals(claim(op).turned().denied(), claim(op).denied().turned(),
                    () -> "turning " + op + " round and denying it, either way about");
        }
    }

    /**
     * Which side each order is satisfied on, written out so that the four are the specification.
     *
     * <p>The one derivation from the two facts a cut holds. Every reading that wants the side asks
     * this, and the table is here rather than in any of them.
     */
    @Test
    void anOrderIsSatisfiedOnTheSideItsOwnValueDecides() {
        Map<BinOp, Towards> sides = new LinkedHashMap<>();
        for (BinOp op : SATISFIED_ON.keySet()) {
            sides.put(op, cut(op).satisfyingSide());
        }
        assertEquals(SATISFIED_ON, sides,
                "which side of its line each order is true on");
    }

    /** Turning an order round moves the side it is satisfied on, and so does denying it. Both move
     *  it, so a reading that does one of them and keeps the side it had is a reading whose line has
     *  its sides the wrong way round. */
    @Test
    void turningAndDenyingBothMoveTheSatisfyingSide() {
        for (BinOp op : SATISFIED_ON.keySet()) {
            Towards side = cut(op).satisfyingSide();
            assertEquals(side.opposite(), cut(op).turned().satisfyingSide(),
                    () -> op + " turned round is satisfied on the other side");
            assertEquals(side.opposite(), cut(op).denied().satisfyingSide(),
                    () -> op + " denied is satisfied on the other side");
        }
    }

    /** An order built from the side it is satisfied on is the order that side was read off, which
     *  is what a reader holding the end a bound kept rather than the class its value is in rests
     *  on. */
    @Test
    void anOrderIsWhatItsSatisfyingSideBuildsBack() {
        for (BinOp op : SATISFIED_ON.keySet()) {
            ComparisonClaim.Cut cut = cut(op);
            assertEquals(cut,
                    ComparisonClaim.Cut.satisfiedOn(cut.satisfyingSide(), cut.holdsAtTheValue()),
                    () -> op + " read as a side and built back from it");
        }
    }

    /**
     * What each comparison states as a relation, written out so that the six are the specification.
     *
     * <p>The crossing into the words the numeric reasoning is written in. Every reader that had a
     * table from the operator to a relation is asking for this, and where a table and this part,
     * the reader tells a domain something the source did not write.
     */
    @Test
    void whatEachComparisonStatesIsOneRelation() {
        Map<BinOp, Rel> stated = new LinkedHashMap<>();
        for (BinOp op : STATED.keySet()) {
            stated.put(op, claim(op).statedRelation());
        }
        assertEquals(STATED, stated, "the relation each comparison states of its two sides");
    }

    /** Denying the claim and denying the relation it states are the same relation, which is what
     *  lets a reader deny wherever it meets a negation and cross over once. */
    @Test
    void denyingAClaimAndDenyingWhatItStatesAreOneRelation() {
        for (BinOp op : STATED.keySet()) {
            assertEquals(claim(op).statedRelation().denied(), claim(op).denied().statedRelation(),
                    () -> "denying " + op + " before and after crossing to a relation");
        }
    }

    /**
     * Turning a comparison round is reading the same statement with the difference the other way
     * about.
     *
     * <p>The law the whole crossing rests on, and the only one that can catch a reader taking the
     * difference the wrong way round: read where the two sides stand at each other every comparison
     * agrees with its own turn, so a reading whose sides are exchanged is right about the
     * equalities and wrong about every ordering.
     */
    @Test
    void turningAComparisonRoundIsTheSameStatementAboutTheOtherDifference() {
        for (BinOp op : STATED.keySet()) {
            for (int sign = -1; sign <= 1; sign++) {
                int stood = sign;
                assertEquals(claim(op).statedRelation().holds(sign),
                        claim(op).turned().statedRelation().holds(-sign),
                        () -> op + " where the left stands " + stood + " to the right, and turned"
                                + " round where it stands " + -stood);
            }
        }
    }

    /**
     * A relation written down is a comparison stating it, and every relation can be written down.
     *
     * <p>The way back, and the whole of it. A reading that composes a comparison out of what the
     * rules proved has a relation and needs what such a comparison places. Asked of every relation
     * rather than of the ones some operator happens to state: what is composed comes from the
     * numeric reasoning, which has all six whether or not an author wrote them.
     */
    @Test
    void everyRelationIsPlacedByAClaimStatingIt() {
        for (Rel rel : Rel.values()) {
            assertEquals(rel, ComparisonClaim.stating(rel).statedRelation(),
                    () -> rel + " taken as what it places, and read back for what it states");
        }
    }

    /**
     * And a claim read for what it states and taken back from that is the claim it was, which is
     * what makes the way back an answer at all.
     *
     * <p>The other direction says the relation survives the crossing; this one says the claim does.
     * Without it two claims could state one relation — an order and the equality at its edge, say —
     * and a reading composing a comparison from that relation would place a partition the rules
     * never proved while every relation still read back as itself.
     *
     * <p>Asked of every claim and not of the ones some operator states. The crossing this law is
     * about has no operator in it, so a claim reachable from no operator would fall outside a law
     * enumerated from {@link BinOp} while the two directions still looked closed. Which claims there
     * are is what the two shapes are made of, and there are two because the type is sealed to them.
     */
    @Test
    void aClaimTakenBackFromWhatItStatesIsItself() {
        for (ComparisonClaim placed : everyClaim()) {
            assertEquals(placed, ComparisonClaim.stating(placed.statedRelation()),
                    () -> placed + " read for what it states, and placed again from it");
        }
    }

    /** Every claim there is: a value singled out or everything else, and an order by which class
     *  the value it names is in and whether the comparison holds there. */
    private static List<ComparisonClaim> everyClaim() {
        List<ComparisonClaim> all = new ArrayList<>();
        for (boolean holdsAtTheValue : List.of(true, false)) {
            all.add(new ComparisonClaim.Singled(holdsAtTheValue));
            for (Towards valueBelongs : Towards.values()) {
                all.add(new ComparisonClaim.Cut(valueBelongs, holdsAtTheValue));
            }
        }
        return all;
    }

    /** And the two enumerations are the same size, which with the two directions above is what says
     *  the crossing is one to one. A claim shape added without a relation to state, or a relation
     *  added with no claim, lands here. */
    @Test
    void thereAreAsManyClaimsAsThereAreRelations() {
        assertEquals(Rel.values().length, everyClaim().size(),
                "every relation places a claim and every claim states a relation, so a claim"
                        + " reachable from no relation is one the way back cannot answer for");
    }

    /**
     * A cut has a side or is not built.
     *
     * <p>The side is one of two answers, and a reference can hold neither. Every reader here asks
     * which side by comparing it to one of the two, so an absent side is read as the other and an
     * order nothing stated is answered about all the way down.
     */
    @Test
    void aCutWithNoSideIsRefused() {
        assertThrows(NullPointerException.class,
                () -> new ComparisonClaim.Cut(null, true),
                "a cut whose named value is in neither class is not a cut");
    }

    private static ComparisonClaim claim(BinOp op) {
        return assertInstanceOf(ComparisonClaim.class, ComparisonPlacement.of(op),
                () -> op + " compares its two sides, so it placed something");
    }

    private static ComparisonClaim.Cut cut(BinOp op) {
        return assertInstanceOf(ComparisonClaim.Cut.class, ComparisonPlacement.of(op),
                () -> op + " orders the values either side of what it names");
    }
}
