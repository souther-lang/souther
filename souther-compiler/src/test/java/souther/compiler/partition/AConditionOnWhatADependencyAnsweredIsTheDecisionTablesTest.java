package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.StandingQuestion;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Weakening;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.AdequacyReport.AdequacyStatus;
import souther.compiler.report.AdequacyUncertainty;

import java.util.LinkedHashSet;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A condition about what a dependency answered is the decision table's, and the reading of the
 * input does not report it as a rule nobody read.
 *
 * <p>A row controls two things: what it writes at the input and what it stands a dependency in
 * with. The reading of the input draws lines on the first; the decision table names distinctions
 * over both. So a reading of the input that reads nothing of {@code known(name)} has met a subject
 * that is not its own, and saying it could not read it held a verdict open over a distinction the
 * table had named and seen both ways of.
 *
 * <p>Handed over, and not dropped: the condition is a column of the table, which owes rows for
 * each way through it ({@link ADecisionIsDrawnOnWhatARowControlsTest}).
 *
 * <p>And only what the table names. A call to a behavior nothing stands in, or an operation of the
 * language, is no subject a row controls, and a condition over one is as unread as it was.
 */
class AConditionOnWhatADependencyAnsweredIsTheDecisionTablesTest {

    private static final String WITHDRAW = """
            module probe.g2
            data Amount = Int
                invariant value >= 0
            data Req = { amount: Amount }
            behavior read : (n: Int) -> Amount | Missing
            behavior withdraw : (r: Req) -> Int
                depends on read
            let withdraw (r, read) =
                match read(1) with
                    | Missing -> 0
                    | Amount as current -> if current.value >= r.amount.value then 1 else 2
            example withdraw
                | "no account" : (Req { amount = Amount(3) }) with read = Missing -> 0
                | "enough" : (Req { amount = Amount(3) }) with read = Amount(5) -> 1
                | "exactly enough" : (Req { amount = Amount(5) }) with read = Amount(5) -> 1
                | "short" : (Req { amount = Amount(6) }) with read = Amount(5) -> 2
                | "zero asked" : (Req { amount = Amount(0) }) with read = Amount(0) -> 1
            example read
                | "one" : (1) -> Amount(5)
                | "none" : (2) -> Missing
            """;

    private static final String GREET = """
            module probe.d
            behavior known : (name: String) -> Bool
            behavior greet : (name: String) -> Int
                depends on known
            let greet (name, known) = if CONDITION then 1 else 0
            example greet
                | "known" : ("a") with known = true -> HELD
                | "unknown" : ("b") with known = false -> DENIED
            """;

    /** A comparison of an answer against the input is no rule of the input's, and every row the
     *  table asks for is written. */
    @Test
    void aComparisonOfAnAnswerWithTheInputIsTheTables() {
        AdequacyReport report = measured(WITHDRAW);

        assertEquals(Set.of(), unreadAt(report));
        assertEquals(AdequacyStatus.SATISFIED, report.adequacy(),
                () -> "what keeps it open: " + report.whatKeepsTheVerdictOpen());
    }

    /** A truth of an answer is the table's however it is spelled, and through a name. */
    @Test
    void aTruthOfAnAnswerIsTheTables() {
        for (String spelled : new String[] {"known(name)", "known(name) == false",
                "{ let k = known(name)\n    k }"}) {
            boolean denied = spelled.contains("false");
            AdequacyReport report = measured(GREET.replace("CONDITION", spelled)
                    .replace("HELD", denied ? "0" : "1").replace("DENIED", denied ? "1" : "0"));

            assertEquals(Set.of(), unreadAt(report), spelled);
            assertEquals(AdequacyStatus.SATISFIED, report.adequacy(),
                    () -> spelled + ": " + report.whatKeepsTheVerdictOpen());
        }
    }

    /** Taken part by part: beside an answer, an operation of the language is unread where it was. */
    @Test
    void anOperationBesideAnAnswerIsStillUnread() {
        AdequacyReport report = measured("""
                module probe.d
                behavior known : (name: String) -> Bool
                behavior greet : (name: String, xs: List<Int>) -> Int
                    depends on known
                let greet (name, xs, known) =
                    if known(name) && List.contains(0, xs) then 1 else 0
                example greet
                    | "both" : ("a", [0]) with known = true -> 1
                    | "unknown" : ("b", [0]) with known = false -> 0
                    | "no zero" : ("a", [1]) with known = true -> 0
                """);

        assertEquals(Set.of("xs"), unreadAt(report),
                "the containment is unread at the list, and the answer is filed nowhere");
    }

    /** A behavior nothing stands in is not a dependency, and a fork on its answer is unread. */
    @Test
    void aCallNoRowStandsInIsStillUnread() {
        AdequacyReport report = measured("""
                module probe.d
                behavior known : (flag: Bool) -> Bool
                let known (flag) = flag
                behavior greet : (flag: Bool) -> Int
                let greet (flag) = if known(flag) then 1 else 0
                example known
                    | "set" : (true) -> true
                    | "clear" : (false) -> false
                example greet
                    | "known" : (true) -> 1
                    | "unknown" : (false) -> 0
                """);

        assertEquals(Set.of("flag"), unreadAt(report));
    }

    private static AdequacyReport measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation);
    }

    /** Where the rules nothing could read are filed, among what keeps the verdict open. */
    private static Set<String> unreadAt(AdequacyReport report) {
        Set<String> out = new LinkedHashSet<>();
        for (AdequacyUncertainty each : report.whatKeepsTheVerdictOpen()) {
            if (each instanceof AdequacyUncertainty.ByWeakening(var cause)
                    && cause instanceof Weakening.ModelReadingIncomplete incomplete
                    && incomplete.cause() instanceof ClosureGap.QuestionUnanswered asked
                    && asked.question() instanceof StandingQuestion.NothingClassifiesIt rule) {
                out.add(rule.at().toString());
            }
        }
        return out;
    }
}
