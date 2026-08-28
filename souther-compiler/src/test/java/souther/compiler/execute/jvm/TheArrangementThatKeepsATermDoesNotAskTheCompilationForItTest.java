package souther.compiler.execute.jvm;

import souther.compiler.WhatWasCompiled;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An arrangement is handed the term and does not go looking for it.
 *
 * <p>What a run is held to is the compile's and reaches the machine as an argument:
 * {@link JvmExampleDeadlines#forThisCompile} takes the wait. An arrangement that reached back into
 * the compilation for it instead would have two ways to learn one thing, and that is not a
 * hypothetical — the wait was read out of the store beside a deadline set there, so the boundary
 * stated a minute while the run was being given up on after five milliseconds.
 *
 * <p>The other half of {@code NoInputOfACompilationIsOneMachinesArrangementTest}, and the half a
 * walk over an input's types cannot answer. That one reads what an input carries, which catches an
 * input whose value is the machine's. It cannot catch {@code Input<Long>} holding a number of bytes
 * of a thread's stack, because nothing about {@code Long} says so — and that is the one that was
 * there. This asks from the end where the type is not the evidence: whatever the key is called, an
 * arrangement may not come to the store to read it.
 *
 * <p><b>Read from what was compiled, not from what was written.</b> An arrangement is anything that
 * answers {@link JvmExampleDeadlines}, and the ways to answer an interface are not one spelling: a
 * class implements it, an anonymous body implements it, a lambda answers it and says neither word.
 * A rule that looked for {@code implements JvmExampleDeadlines} would hold for the three that are
 * here and let the fourth past — and the fourth is the easy one to write, because a lambda that
 * closes over a store is a line long.
 */
class TheArrangementThatKeepsATermDoesNotAskTheCompilationForItTest {

    /** How this compiler holds and answers its own questions. */
    private static final List<String> THE_STORE = List.of(
            "souther.compiler.query.Db",
            "souther.compiler.query.Front",
            "souther.compiler.query.Output",
            "souther.compiler.query.Key");

    /**
     * No arrangement names the store.
     */
    @Test
    void nothingThatKeepsATermReadsTheCompilationsAnswers() {
        List<String> naming = new ArrayList<>();
        for (String arrangement : arrangements()) {
            for (String named : WhatWasCompiled.typesNamedBy(arrangement)) {
                if (THE_STORE.stream().anyMatch(store -> named.equals(store)
                        || named.startsWith(store + "$"))) {
                    naming.add(arrangement + " names " + named);
                }
            }
        }

        assertEquals(List.of(), naming,
                "an arrangement keeps the term it is handed; reading one out of the store is the"
                        + " second answer that JvmExampleDeadlines exists to do without");
    }

    /**
     * And the walk finds the arrangements there are.
     *
     * <p>Not the set of them. What the rule holds is every answer of this interface, whatever it is
     * called and wherever it is written, so pinning a list here would put the rule back in a name
     * again. What is pinned is that the three there are today were found: a walk that had gone blind
     * would report nothing and pass.
     */
    @Test
    void andTheWalkFindsTheArrangementsThereAre() {
        Set<String> found = arrangements();

        assertTrue(found.containsAll(Set.of(
                        "souther.compiler.execute.jvm.JvmDeadlines",
                        "souther.compiler.query.ChosenJvmExampleDeadlines",
                        "souther.compiler.examples.CallerCrossingDeadlines")),
                () -> "the ones there are should be among what was walked: " + found);
    }

    /** Every class that answers {@link JvmExampleDeadlines}, including the one a lambda of it was
     *  written in. */
    private static Set<String> arrangements() {
        return WhatWasCompiled.answering(JvmExampleDeadlines.class);
    }
}
