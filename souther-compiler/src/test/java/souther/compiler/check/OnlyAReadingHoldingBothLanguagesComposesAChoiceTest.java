package souther.compiler.check;

import souther.compiler.WhatWasCompiled;
import souther.compiler.numeric.OrderedIntervals;
import souther.compiler.values.PlannedValues;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashSet;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Who may compose what a choice leaves, in one language at a time.
 *
 * <p>A conjunction is componentwise: what two clauses leave a position is what each language says
 * they leave it, and a language meeting two of its own readings is answering its own question. A
 * choice is not. Which alternatives anybody can take is a fact about the whole of what was read —
 * a branch no order admits beside a branch no set of values admits is a choice with nothing in it,
 * and neither language alone finds anything wrong with the branch the other one refused.
 *
 * <p>So the operations below take an answer rather than work one out. Every alternative dead, and
 * both alternatives standing, are two proofs the whole state already holds; the component is told
 * which of them it is realising. One alternative dead asks the components nothing, because what the
 * choice leaves is the standing alternative, which the holder has in hand.
 *
 * <p>That is why these have callers and {@code meet} has none listed: a rule confining the
 * conjunction would be a rule about arithmetic that is sound wherever it is written.
 *
 * <p>Read off the compiled classes. A call is in the caller's constant pool however it is spelled,
 * and a lambda's body is compiled into the class that wrote it, so this cannot be got out of by
 * writing the call somewhere shorter.
 */
class OnlyAReadingHoldingBothLanguagesComposesAChoiceTest {

    /**
     * The one place both languages are held while a choice is composed.
     *
     * <p>A reading of a declaration's clauses is a pair — which values each position may take, and
     * where each of them stops — and this is the pair. What decides a branch's fate reads both of
     * them ({@code Confinement.admission}), and what realises the decision is written here beside
     * that reading.
     */
    private static final String HOLDER = "souther.compiler.check.Confinement$Planned";

    /** What a choice comes to, in one language, once its alternatives' fates are known. */
    private record ChoiceOperation(Class<?> on, String called) {}

    private static final Set<ChoiceOperation> OF_A_CHOICE = Set.of(
            new ChoiceOperation(PlannedValues.class, "joinLive"),
            new ChoiceOperation(PlannedValues.class, "joinLiveApart"),
            new ChoiceOperation(PlannedValues.class, "bothDead"),
            new ChoiceOperation(OrderedIntervals.class, "joinLive"),
            new ChoiceOperation(OrderedIntervals.class, "bothDead"));

    @Test
    void nothingButTheReadingHoldingBothLanguagesComposesAChoice() {
        Set<String> elsewhere = new LinkedHashSet<>();
        for (ChoiceOperation each : OF_A_CHOICE) {
            for (String caller : WhatWasCompiled.callersOf(each.on(), each.called())) {
                if (!caller.equals(HOLDER)) {
                    elsewhere.add(caller + " calls " + each.on().getSimpleName()
                            + "." + each.called());
                }
            }
        }

        assertEquals(Set.of(), elsewhere,
                "a choice composed where one language is held is a choice settled by that language");
    }

    /**
     * And each of them is reached, so the rule above is about calls that happen.
     *
     * <p>A confinement over an operation nobody calls passes whatever the code does. Asked
     * separately from the rule, so that an operation falling out of use is a finding here and not a
     * silence there.
     */
    @Test
    void eachOfThemIsWhatTheHolderComposesWith() {
        for (ChoiceOperation each : OF_A_CHOICE) {
            assertTrue(WhatWasCompiled.callersOf(each.on(), each.called()).contains(HOLDER),
                    each.on().getSimpleName() + "." + each.called() + " is composed with");
        }
    }
}
