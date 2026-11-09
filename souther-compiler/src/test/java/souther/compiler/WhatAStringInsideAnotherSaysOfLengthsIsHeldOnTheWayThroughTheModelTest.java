package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a string standing inside another says of how long each is, on the side it came out, is held
 * of a way through a body the way a guard on the lengths says it.
 *
 * <p>The way is read off what the model states, and a call of {@code String.contains},
 * {@code startsWith} or {@code endsWith} states one string standing inside another, and a piece of
 * a string held to a pattern states the string in a language of its own. A branch that needs the
 * lengths to be what that rules out is one no value reaches, which the account says of its decision
 * rule; the same branch beside a length the statement allows is not.
 *
 * <p>A pattern a call of {@code String.matches} is written with over a string of the row is not
 * among them: the model reads it as a statement the decision reads of the row, and it is no fact of
 * a way. So what such a call says of the lengths is taken where a guard is read and where an
 * invariant is assumed, and not here.
 */
class WhatAStringInsideAnotherSaysOfLengthsIsHeldOnTheWayThroughTheModelTest {

    private static final String NO_VALUE_REACHES_IT = "but no value can reach it coming out so";

    /**
     * A body of {@code f}, what it answers for {@code s = "aa"} and {@code t = "b"} — the one row
     * the model states — and whether the account says a decision rule of it no value reaches.
     */
    private record Row(String body, String answer, boolean unreachable) {}

    private static final List<Row> ROWS = List.of(
            // Not standing inside, the one looked for is not empty, whichever way it is looked for.
            new Row("if String.contains(t, s) then B else "
                    + "(if String.length(t) == 0 then A else C)", "C", true),
            new Row("if String.contains(t, s) then B else "
                    + "(if String.length(t) == 1 then A else C)", "A", false),
            new Row("if String.startsWith(t, s) then B else "
                    + "(if String.length(t) == 0 then A else C)", "C", true),
            new Row("if String.endsWith(t, s) then B else "
                    + "(if String.length(t) == 0 then A else C)", "C", true),
            // Standing inside, it is no longer than the one around it, and that is all it says.
            new Row("if String.contains(t, s) then "
                    + "(if String.length(t) > String.length(s) then A else B) else C", "C", true),
            new Row("if String.contains(t, s) then "
                    + "(if String.length(t) == String.length(s) then A else B) else C", "C",
                    false),
            // Neither side says it of the other: not standing inside says nothing of how long
            // either is beside the other.
            new Row("if String.contains(t, s) then B else "
                    + "(if String.length(t) > String.length(s) then A else C)", "C", false),
            // A string with a character in a language is in the language of the strings holding
            // one, which is none of them empty.
            new Row("if List.any(p -> String.matches(\"[0-9]{3}\", p), String.split(\",\", s)) "
                    + "then (if String.length(s) == 0 then A else B) else C", "C", true),
            new Row("if List.any(p -> String.matches(\"[0-9]{3}\", p), String.split(\",\", s)) "
                    + "then (if String.length(s) == 3 then A else B) else C", "C", false));

    @Test
    void eachBodyIsSaidToBeReachedOrNotAsTheLengthsItNeedsAreAllowed() {
        List<String> wrong = new ArrayList<>();
        for (Row row : ROWS) {
            boolean said = accountOf(row).contains(NO_VALUE_REACHES_IT);
            if (said != row.unreachable()) {
                wrong.add(row.body() + " is said unreachable: " + said);
            }
        }
        assertEquals(List.of(), wrong, "each body is said what the lengths leave open");
    }

    private static String accountOf(Row row) {
        Compilation compilation = Compilation.ofSource("""
                module demo

                data Tag = A | B | C

                behavior f : (s: String, t: String) -> Tag
                let f (s, t) =
                    %s

                example f
                    | ("aa", "b") -> %s
                """.formatted(row.body(), row.answer()), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code().toString()).toList(),
                row.body() + " compiles");
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
