package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.AdequacyReport.AdequacyStatus;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

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

    private static final JsonMapper JSON = JsonMapper.builder().build();

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

    /** A comparison of an answer with the input is no rule of the input's, and every row the
     *  table asks for is written. */
    @Test
    void aComparisonOfAnAnswerWithTheInputIsTheTables() {
        AdequacyReport report = measured(WITHDRAW);

        assertEquals(Set.of(), notReadAt(report));
        assertEquals(AdequacyStatus.SATISFIED, report.adequacy(),
                () -> "what keeps it open: " + report.whatKeepsTheVerdictOpen());
    }

    /** A truth of an answer is the table's however it is spelled, and through a name. */
    @Test
    void aTruthOfAnAnswerIsTheTables() {
        for (String spelled : new String[] {"known(name)", "known(name) == false",
                "Bool.not(known(name))", "Bool.not(known(name)) == true",
                "{ let k = known(name)\n    k }"}) {
            boolean denied = spelled.contains("false") || spelled.contains("not");
            AdequacyReport report = measured(GREET.replace("CONDITION", spelled)
                    .replace("HELD", denied ? "0" : "1").replace("DENIED", denied ? "1" : "0"));

            assertEquals(Set.of(), notReadAt(report), spelled);
            assertEquals(AdequacyStatus.SATISFIED, report.adequacy(),
                    () -> spelled + ": " + report.whatKeepsTheVerdictOpen());
        }
    }

    /**
     * And a dependency asked about what another one answered, through the name an arm gave it:
     * the question is the table's whatever it was asked about.
     */
    @Test
    void anAnswerAskedAboutAnotherAnswerIsTheTables() {
        AdequacyReport report = measured("""
                module probe.v
                data User = { hash: String }
                data Credentials = { name: String, password: String }
                behavior findUser : (name: String) -> User | NoUser
                behavior verifyPassword : (password: String, hash: String) -> Bool
                behavior login : (c: Credentials) -> Int
                    depends on findUser, verifyPassword
                let login (c, findUser, verifyPassword) =
                    match findUser(c.name) with
                        | NoUser -> 0
                        | User as found ->
                            if verifyPassword(c.password, found.hash) then 1 else 2
                example login
                    | "none" : (Credentials { name = "x", password = "p" })
                        with findUser = NoUser, verifyPassword = false -> 0
                    | "ok" : (Credentials { name = "x", password = "p" })
                        with findUser = User { hash = "h" }, verifyPassword = true -> 1
                    | "bad" : (Credentials { name = "x", password = "p" })
                        with findUser = User { hash = "h" }, verifyPassword = false -> 2
                """);

        assertEquals(Set.of(), notReadAt(report));
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

        assertEquals(Set.of("xs"), notReadAt(report),
                "the containment is unread at the list, and the answer is filed nowhere");
    }

    /**
     * A behavior nothing stands in is not a dependency: a fork on its answer is read through its
     * body, where the call stands, and comes to the truth of what the call handed it.
     */
    @Test
    void aCallNoRowStandsInIsReadThroughTheBodyItCalls() {
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

        assertEquals(Set.of(), notReadAt(report));
    }

    /**
     * The name an arm gives a value the body built is not read through to that value.
     *
     * <p>What was built is every case it could be, and read without the arm {@code b.k} would be
     * the choice between them — a rule about {@code flag} the body never wrote. What the name is
     * read through to is an answer, which holds nothing a reader could look inside.
     */
    @Test
    void aNameForABuiltValueIsNotReadThroughToIt() {
        AdequacyReport report = measured("""
                module probe.c
                data A = { n: Int }
                data B = { k: Int }
                data S = A | B
                behavior use : (flag: Bool) -> Int
                let use (flag) =
                    match (if flag then A { n = 1 } else B { k = 2 }) with
                        | A as a -> if a.n > 0 then 1 else 2
                        | B as b -> if b.k > 0 then 3 else 4
                example use
                    | "a" : (true) -> 1
                    | "b" : (false) -> 3
                """);

        assertEquals(Set.of(), notReadAt(report));
    }

    private static AdequacyReport measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation);
    }

    /** The positions the report says a rule went unread about, over every behavior. */
    private static Set<String> notReadAt(AdequacyReport report) {
        JsonNode root = JSON.readTree(report.json(SourceRendering.namedByIdentity(
                SourceLayouts.NONE)));
        Set<String> out = new LinkedHashSet<>();
        for (JsonNode module : root.path("modules")) {
            for (JsonNode behavior : module.path("behaviors")) {
                for (JsonNode unread : behavior.path("partition").path("notRead")) {
                    out.add(unread.path("position").asString());
                }
            }
        }
        return out;
    }
}
