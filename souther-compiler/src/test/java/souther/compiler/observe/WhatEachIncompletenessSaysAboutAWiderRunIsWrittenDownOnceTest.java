package souther.compiler.observe;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Every reason a measure could not read what it needed, and what it says about a wider run.
 *
 * <p>The switch already refuses a code nobody answered for: {@link Incompleteness.Code#runSensitivity}
 * has no {@code default}, so a tenth is a build failure. What it cannot refuse is a code moved from
 * one answer to the other, and the difference is what a person does next — measure the same model
 * again allowing more, or not.
 *
 * <p><b>Which is why the rows are here and not derived.</b> A code answers this only because every
 * producer of it agrees about it, and that is a property of the producers rather than of the word.
 * Where they did not agree the code was split: a row a figure stopped and a row the evaluation had
 * no answer for were {@code ROW_UNDECIDED} between them, and no answer here could have been right
 * at both. A row added below with the wrong word is one somebody has to have written.
 */
class WhatEachIncompletenessSaysAboutAWiderRunIsWrittenDownOnceTest {

    /** Every code, and whether a run of this compiler allowed more could come to another answer. */
    private static Map<String, String> theCodes() {
        Map<String, String> table = new LinkedHashMap<>();
        // Nothing could read the value back. A reading allowed more nodes reads back exactly as
        // much of it.
        table.put("VALUE_UNREADABLE", "UNAFFECTED");
        // And the one beside it, which is the same loss from a figure: the observation walked as
        // far as its nodes, its depth and its text allowed. The two have been apart since before
        // this question was asked, for this reason said as what an author does — one goes away if
        // the fixture is written smaller and the other does not.
        table.put("VALUE_TRUNCATED", "MAY_CHANGE");
        // The evaluation had no answer for the row.
        table.put("ROW_UNDECIDED", "UNAFFECTED");
        // And the row stopped by the steps, the depth or the clock it is evaluated under, each of
        // which is a figure `EvaluationPolicy` holds.
        table.put("ROW_EVALUATION_LIMIT_REACHED", "MAY_CHANGE");
        // Nothing could establish that what answers the behavior was built against this model,
        // which is two builds disagreeing or an answer nothing could read. Neither is a figure.
        table.put("ANSWERER_NOT_ESTABLISHED", "UNAFFECTED");
        // The classes would not link, which is the host and not an allowance: a run allowed more on
        // the same machine raises the same error.
        table.put("LINKAGE_FAILED", "UNAFFECTED");
        table.put("OBSERVATION_ABSENT", "UNAFFECTED");
        table.put("INSTRUMENTATION_ABSENT", "UNAFFECTED");
        return table;
    }

    /** The table, held against what the codes answer, with the population read off the enum. */
    @Test
    void everyCodeSaysWhetherAWiderRunCouldAnswerIt() {
        Map<String, String> said = new LinkedHashMap<>();
        for (Incompleteness.Code each : Incompleteness.Code.values()) {
            said.put(each.name(), each.runSensitivity().name());
        }

        assertEquals(theCodes(), said);
    }
}
