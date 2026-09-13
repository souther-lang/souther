package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether the search answers a thing with a row does not turn on how the names of a union's cases
 * compare.
 *
 * <p>Beside what the rows settle, and below it. A search that reached an arm under one spelling of
 * the cases and not the other can be covered up downstream — another row happening to go through
 * the arm settles it either way — and what a reader is told about their model would still be two
 * answers: this arm is one nothing could compose a row for, or it is not.
 *
 * <p>So this holds the search's own answer. For every class and every arm the run was asked about,
 * whether it came back with a row is compared, and which row it named is not: two searches finding
 * a row apiece have found what there is to find, whichever of them the answer is written with.
 *
 * <p>The two models are one text with the case names exchanged for names of the same length, so the
 * obligations are the same obligations and what differs is the order the names compare in. The
 * exchange reverses it.
 */
class WhatTheSearchAnswersForDoesNotTurnOnHowCaseNamesCompareTest {

    /**
     * A body whose way into one case's arms is a truth read off a place inside the answer, which is
     * a condition no demand states.
     *
     * <p>So nothing composes a row to go down them, and whether they are reached at all follows
     * from what the rows composed for the input's own points stand the dependency in with.
     */
    private static final String MODEL = """
            module example.answered

            data Yes
            data No
            data Answer = Yes | No

            data Blocked = Int
            data Cleared = { ok: Bool }

            behavior lookup : (id: Int) -> Blocked | Cleared

            behavior decides : (id: Int) -> Answer
                depends on lookup
            let decides (id, lookup) =
                if id > 5 then
                    match lookup(id) with
                        | Blocked -> No
                        | Cleared { ok } -> if ok then Yes else No
                else No

            example decides
                | (0) with lookup = Blocked(1) -> No
            """;

    /** The same names at the same width, comparing the other way round. */
    private static final Map<String, String> THE_OTHER_WAY = Map.of(
            "Blocked", "Refused",
            "Cleared", "Allowed");

    @Test
    void oneModelSpelledTwoWaysIsAnsweredForTheSameWay() {
        Map<String, String> asWritten = answeredFor(MODEL);
        Map<String, String> respelled = answeredFor(respelled(MODEL));

        assertFalse(asWritten.isEmpty(), "the run was asked about something");
        assertEquals(asWritten.keySet(), respelled.keySet(),
                "the two spellings are asked about the same things");
        List<String> moved = new ArrayList<>();
        asWritten.forEach((owed, answer) -> {
            if (!answer.equals(respelled.get(owed))) {
                moved.add(owed + ": " + answer + " and " + respelled.get(owed));
            }
        });
        assertEquals(List.of(), moved,
                "answered with a row under one spelling of the cases and not the other");
    }

    /**
     * Whether each thing the run was asked about came back with a row, under the name the plan asks
     * by.
     *
     * <p>The kind of answer and not the row, because which row answers is what several searches
     * finding one apiece leave to whoever offers them.
     */
    private static Map<String, String> answeredFor(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        String module = compilation.modules().get(0);
        Map<String, Adequacy.Filling> filled = Adequacy.generatedOf(compilation.db(), module);
        assertTrue(filled != null && !filled.isEmpty(), "the module is searched");
        Map<String, String> out = new TreeMap<>();
        filled.forEach((behavior, filling) -> {
            filling.composed().discharge().classes().forEach((owed, answer) ->
                    out.put(behavior + " class " + owed, kindOf(answer)));
            filling.composed().discharge().arms().forEach((owed, answer) ->
                    out.put(behavior + " arm " + owed, kindOf(answer)));
        });
        return out;
    }

    /** What kind of answer it is, which is what a reader of the account acts on. */
    private static String kindOf(Object disposition) {
        return disposition.getClass().getSimpleName();
    }

    private static String respelled(String model) {
        String out = model;
        for (Map.Entry<String, String> each : THE_OTHER_WAY.entrySet()) {
            out = out.replace(each.getKey(), each.getValue());
        }
        return out;
    }
}
