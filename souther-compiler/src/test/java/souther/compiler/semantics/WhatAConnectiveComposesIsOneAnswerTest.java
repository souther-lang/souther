package souther.compiler.semantics;

import org.junit.jupiter.api.Test;
import souther.compiler.types.BinOp;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The algebra of what a connective composes, which is what lets a reader stop holding the operator.
 *
 * <p>Each law is what some reading rests on. That the composition and
 * {@link BinOp#joinsTwoConditions} agree is what makes a composition the evidence that an operator
 * joins two conditions. That denying it exchanges the two answers is what lets a reader meeting a
 * negation deny what it holds rather than working out which operator would have been written. And
 * that a composition under a polarity is that same exchange is what lets a reader carry a polarity
 * without an operator table of its own.
 */
class WhatAConnectiveComposesIsOneAnswerTest {

    /** What each connective composes where it is stated. Written out here and nowhere else in the
     *  compiler: every reader asks for this, and this is the table that says which answer it is. */
    private static final Map<BinOp, ConditionJoin> STATED = stated();

    /** What each composition comes to where the condition it joins is denied. Written out here and
     *  nowhere in the compiler: what a reading does under a negation is deny the composition, and
     *  this is the table that says the two are one. */
    private static final Map<ConditionJoin, ConditionJoin> DENIED = denied();

    private static Map<BinOp, ConditionJoin> stated() {
        Map<BinOp, ConditionJoin> composed = new LinkedHashMap<>();
        composed.put(BinOp.AND, ConditionJoin.BOTH);
        composed.put(BinOp.OR, ConditionJoin.EITHER);
        return composed;
    }

    private static Map<ConditionJoin, ConditionJoin> denied() {
        Map<ConditionJoin, ConditionJoin> pairs = new LinkedHashMap<>();
        pairs.put(ConditionJoin.BOTH, ConditionJoin.EITHER);
        pairs.put(ConditionJoin.EITHER, ConditionJoin.BOTH);
        return pairs;
    }

    /** An operator composes something exactly where it joins two conditions. Two spellings of one
     *  membership drift, and an operator added to the language would land in them differently. */
    @Test
    void whatComposesSomethingIsWhatJoinsTwoConditions() {
        Map<BinOp, Boolean> composes = new LinkedHashMap<>();
        Map<BinOp, Boolean> joins = new LinkedHashMap<>();
        for (BinOp op : BinOp.values()) {
            composes.put(op, ConditionJoin.of(op).isPresent());
            joins.put(op, op.joinsTwoConditions());
        }
        assertEquals(joins, composes,
                "what an operator composes and whether it joins two conditions are one question");
    }

    /**
     * What each connective composes where it is stated, written out so that the two are the
     * specification.
     *
     * <p>The one crossing from how a condition is written to what it says of its two halves. Every
     * reader that had a table from the operator to a composition is asking for this, and where a
     * table and this part, the reader takes a condition apart the source did not write.
     */
    @Test
    void whatEachConnectiveStatesIsOneComposition() {
        Map<BinOp, ConditionJoin> composed = new LinkedHashMap<>();
        for (BinOp op : STATED.keySet()) {
            composed.put(op, ConditionJoin.of(op).orElseThrow());
        }
        assertEquals(STATED, composed, "what each connective makes of the two conditions it joins");
    }

    /** An operator that joins no two conditions composes nothing, which is what lets a reading of
     *  any binary ask before it knows whether it is a connective. */
    @Test
    void anOperatorThatJoinsNoConditionsComposesNothing() {
        for (BinOp op : BinOp.values()) {
            if (op.joinsTwoConditions()) {
                continue;
            }
            assertEquals(Optional.empty(), ConditionJoin.of(op),
                    () -> op + " joins no two conditions, so it composes nothing");
        }
    }

    /** Denying a condition exchanges the two answers, which is the whole of what a denial does to a
     *  connective and the reason no reader works it out beside the operator. */
    @Test
    void denyingAConditionExchangesWhatItsConnectiveComposes() {
        for (Map.Entry<ConditionJoin, ConditionJoin> each : DENIED.entrySet()) {
            assertEquals(each.getValue(), each.getKey().denied(),
                    () -> each.getKey() + " denied composes " + each.getValue());
        }
    }

    /** Denying twice is the composition, which is what lets a reading deny wherever it meets a
     *  negation rather than counting how many it is under. */
    @Test
    void denyingTwiceLeavesTheComposition() {
        for (ConditionJoin join : ConditionJoin.values()) {
            assertEquals(join, join.denied().denied(),
                    () -> "denying " + join + " twice composes what it composed");
        }
    }

    /** A stated condition composes what its connective composes, and a denied one composes the
     *  denial of it. The polarity a reader carries is applied to the composition and nowhere to the
     *  operator. */
    @Test
    void aCompositionUnderAPolarityIsTheStatementOrItsDenial() {
        for (ConditionJoin join : ConditionJoin.values()) {
            assertEquals(join, join.under(true),
                    () -> join + " stated composes what it composes");
            assertEquals(join.denied(), join.under(false),
                    () -> join + " denied composes the other one");
        }
    }
}
