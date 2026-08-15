package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Db;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which cases are named as unverified, decided from what the rows saw.
 *
 * <p>Naming a case as one nothing confirmed is worth saying where some case was confirmed and the
 * rest were not. Where nothing was seen to be produced at all, every case is unverified and naming
 * each of them repeats the one thing the run has to say, which the rows already say in their own
 * right. What separates the two is whether any row observed the behavior answer — not whether the
 * behavior is written with a {@code let}, which is a different question that happens to agree with
 * this one while the only thing that applies a behavior is the compile that generated it.
 */
class WhatIsUnverifiedComesFromWhatTheRowsObservedTest {

    /**
     * A run that observed one case names the others, and does not name the one it observed.
     *
     * <p>The boundary itself: {@code Approved} is confirmed and stays unnamed, {@code Rejected} is
     * expected by a row and was never produced, so it is named. A guard that read anything wider than
     * the rows would either lose the second or add the first.
     */
    @Test
    void aCaseNoRowConfirmedIsNamedWhereAnotherCaseWasObserved() {
        String source = """
                module example.decide

                data Yes
                data No
                data Flag = Yes | No

                data Approved = { note: String }
                data Rejected = { note: String }

                behavior decide : (f: Flag) -> Approved | Rejected
                    constructs Approved, Rejected
                let decide (f) =
                    match f with
                        | Yes -> Approved { note = "yes" }
                        | No  -> Rejected { note = "no" }

                example decide
                    | "holds"     : (Yes) -> Approved { note = "yes" }
                    | "disagrees" : (Yes) -> Rejected { note = "no" }
                """;

        assertEquals(List.of("Rejected"),
                unverified(source, "decide"),
                "the case a row expects and nothing produced is the one worth naming; the case a row "
                        + "confirmed is not");
    }

    /**
     * A behavior with nothing to run it: its rows are recorded, so nothing was observed and no case is
     * named. What the compile can say about such a behavior is that no row expects a case
     * ({@code OUTPUT_CASE_UNSPECIFIED}), which it still says.
     */
    @Test
    void anInjectedBehaviorNamesNoUnverifiedCase() {
        String source = """
                module example.member
                import String ( length )

                data MemberId = String
                    invariant length(value) > 0

                data Found = { id: MemberId }
                data Missing = { reason: String }

                behavior findMember : (id: MemberId) -> Found | Missing

                example findMember
                    | "found" : (MemberId("m-1")) -> Found { id = MemberId("m-1") }
                """;

        assertEquals(List.of(), unverified(source, "findMember"),
                "nothing applied it, so every case is unverified and naming each says nothing");
        assertEquals(List.of("Missing"), unspecified(source, "findMember"),
                "what the rows do and do not ask for is measured the same as anywhere else");
    }

    /**
     * A behavior that has a {@code let} and whose rows all stopped before they could apply it. The
     * run observed nothing, so it says nothing case by case — and what did happen to the rows is
     * reported where it happened, which is a better answer than a list of cases nobody could have
     * covered.
     */
    @Test
    void aBehaviorWhoseRowsNeverRanNamesNoUnverifiedCaseAndSaysWhy() {
        String source = """
                module example.greet
                import String ( length )

                data MemberId = String
                    invariant length(value) > 0

                data Yes
                data No
                data Answer = Yes | No

                data Hello = { who: String }
                data Bye = { who: String }

                behavior asked : (id: MemberId) -> Answer

                behavior greet : (id: MemberId) -> Hello | Bye
                    depends on asked
                    constructs Hello, Bye
                let greet (id, asked) =
                    match asked(id) with
                        | Yes -> Hello { who = "hi" }
                        | No  -> Bye { who = "bye" }

                example greet
                    | "greeted" : (MemberId("m-1")) -> Hello { who = "hi" }
                """;

        assertEquals(List.of(), unverified(source, "greet"),
                "a row that never applied the behavior saw nothing, and a let does not make it a "
                        + "row that did");
        List<String> codes = codes(source);
        assertTrue(codes.contains("E1908"),
                "why the row stopped is reported at the row, which is what the reader is owed here: "
                        + codes);
    }

    /**
     * A run that answered with a value no declaration here names. The behavior was applied and gave
     * something back, so which cases it was not seen to produce is worth naming — and no case can be
     * read off such an answer, so the evidence has an empty {@code observed} and is no measure of
     * whether anything ran.
     *
     * <p>{@code String} is left out of the naming for the reason any unspecified case is: no row asks
     * for it, so it is reported as unspecified instead.
     */
    @Test
    void anAnswerNoDeclarationNamesIsStillAnAnswer() {
        String source = """
                module example.name

                data Missing = { why: String }

                behavior name : (n: Int) -> String | Missing
                    constructs Missing
                let name (n) = if n > 0 then "yes" else Missing { why = "no" }

                example name
                    | "wants Missing, is answered with a String" : (1) -> Missing { why = "no" }
                """;

        assertEquals(List.of("Missing"), unverified(source, "name"),
                "the row ran and was answered; that this compile cannot place the answer is not a "
                        + "reason to stop saying which case nothing confirmed");
    }

    private static List<String> unverified(String source, String behavior) {
        return named(source, behavior, Adequacy.Kind.OUTPUT_CASE_UNVERIFIED);
    }

    private static List<String> unspecified(String source, String behavior) {
        return named(source, behavior, Adequacy.Kind.OUTPUT_CASE_UNSPECIFIED);
    }

    /** The cases one kind of finding names for one behavior, in the order the findings are held. */
    private static List<String> named(String source, String behavior, Adequacy.Kind kind) {
        Compilation compilation = compiled(source);
        Map<String, List<Adequacy.Finding>> all = compilation.db()
                .ask(new Adequacy.Findings(compilation.modules().get(0))).value();
        return all == null ? List.of()
                : all.getOrDefault(behavior, List.of()).stream()
                        .filter(f -> f.kind() == kind)
                        .map(f -> String.valueOf(f.args().get(0)))
                        .toList();
    }

    private static List<String> codes(String source) {
        List<String> codes = new ArrayList<>();
        for (Db.Found found : compiled(source).db().allReports()) {
            String code = found.report().diagnostic().code();
            if (code != null) {
                codes.add(code);
            }
        }
        return codes;
    }

    private static Compilation compiled(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        return compilation;
    }
}
