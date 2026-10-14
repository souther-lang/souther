package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.SourceRendering;
import souther.compiler.report.AdequacyReport;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value of a sum compared with one of its cases asks which case the value is, as an arm of a
 * {@code match} on it does, and owes what that {@code match} owes.
 *
 * <p>No line on the order the cases are declared in: the case declared after the one compared with
 * is no nearer to it than any other. And no combination on a way that never reads the other input:
 * where the reason is not a wrong password the account is handed back unlooked at, whichever way the
 * test of the reason was written.
 */
class ACaseComparedWithAValueIsReadAsAMatchOnItTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String DECLARATIONS = """
            module probe.lock

            data Active
            data Locked
            data Status = Active | Locked
            data WrongPassword
            data Expired
            data Closed
            data Reason = %s
            data Account = { status: Status }

            behavior apply : (account: Account, reason: Reason) -> Account
                constructs Account

            let lock (account: Account): Account =
                match account.status with
                    | Active -> Account { status = Locked }
                    | Locked -> account

            """;

    private static final String ROWS = """

            example apply
                | (Account { status = Active }, WrongPassword) -> Account { status = Locked }
                | (Account { status = Locked }, WrongPassword) -> Account { status = Locked }
                | (Account { status = Active }, Expired) -> Account { status = Active }
                | (Account { status = Active }, %s) -> Account { status = Active }
            """;

    private static final String AS_DECLARED = "WrongPassword | Expired | Closed";

    private static final String MATCH = """
            let apply (account, reason) =
                match reason with
                    | WrongPassword -> lock(account)
                    | Expired | Closed -> account
            """;

    /** The pairs the {@code match} owes: only a wrong password reads the account. */
    private static final Set<String> OWED_BY_THE_MATCH = Set.of(
            "Active × WrongPassword", "Locked × WrongPassword");

    @Test
    void theMatchOwesOnlyThePairsOfTheArmThatReadsBoth() {
        Measured match = measured(AS_DECLARED, MATCH);
        assertEquals(OWED_BY_THE_MATCH, match.owed());
        assertEquals(List.of(), match.borders(), "and its rules draw no line");
    }

    @Test
    void anEqualityOwesWhatTheMatchOwesAndDrawsNoLine() {
        for (String body : List.of(
                "let apply (account, reason) =\n"
                        + "    if reason == WrongPassword then lock(account) else account\n",
                "let apply (account, reason) =\n"
                        + "    if WrongPassword == reason then lock(account) else account\n",
                "let apply (account, reason) =\n"
                        + "    if reason /= WrongPassword then account else lock(account)\n",
                "let apply (account, reason) = {\n"
                        + "    let wrong = WrongPassword\n"
                        + "    if reason == wrong then lock(account) else account\n"
                        + "}\n")) {
            Measured written = measured(AS_DECLARED, body);
            assertEquals(OWED_BY_THE_MATCH, written.owed(), body);
            assertEquals(List.of(), written.borders(), () -> "no line on the order: " + body);
            assertEquals(List.of(), written.pairGaps(), () -> "nothing to refuse: " + body);
        }
    }

    /** The order the cases are declared in says nothing of which one the value is. */
    @Test
    void reorderingTheCasesChangesNothingOwed() {
        Measured reordered = measured("Closed | Expired | WrongPassword",
                "let apply (account, reason) =\n"
                        + "    if reason == WrongPassword then lock(account) else account\n");
        assertEquals(OWED_BY_THE_MATCH, reordered.owed());
        assertEquals(List.of(), reordered.borders());
    }

    /** Under an {@code &&} both tests are of cases, and only the way through both reads both. */
    @Test
    void twoCasesTestedTogetherOweWhatTheirArmsRead() {
        Measured both = measured(AS_DECLARED, "let apply (account, reason) =\n"
                + "    if reason == WrongPassword && account.status == Active"
                + " then Account { status = Locked } else account\n");
        assertEquals(OWED_BY_THE_MATCH, both.owed());
        assertEquals(List.of(), both.borders());
    }

    /**
     * Beside a truth of the input, which the way does not name, the case the comparison came out
     * is read where the arm is: as the {@code match} that asks the truth only under the case.
     */
    @Test
    void aCaseTestedBesideATruthOwesWhatTheMatchUnderItOwes() {
        String head = DECLARATIONS.formatted(AS_DECLARED).replace(
                "(account: Account, reason: Reason)",
                "(account: Account, reason: Reason, urgent: Bool)");
        String rows = """

                example apply
                    | (Account { status = Active }, WrongPassword, true) -> Account { status = Locked }
                    | (Account { status = Locked }, WrongPassword, true) -> Account { status = Locked }
                    | (Account { status = Active }, WrongPassword, false) -> Account { status = Active }
                    | (Account { status = Active }, Expired, true) -> Account { status = Active }
                """;
        Measured both = measuredSource(head + """
                let apply (account, reason, urgent) =
                    if reason == WrongPassword && urgent then lock(account) else account
                """ + rows);
        Measured nested = measuredSource(head + """
                let apply (account, reason, urgent) =
                    match reason with
                        | WrongPassword -> if urgent then lock(account) else account
                        | Expired | Closed -> account
                """ + rows);
        assertEquals(withTheAccount(nested.owed()), withTheAccount(both.owed()));
    }

    /**
     * The pairs of {@code owed} one of which is a class of the account's status: the ones only the
     * arm that locks reads.
     *
     * <p>Only those, because a way out of the {@code &&} the truth leaves unnamed keeps every
     * combination of the two positions it is about, whatever the left was written as.
     */
    private static Set<String> withTheAccount(Set<String> owed) {
        Set<String> out = new LinkedHashSet<>();
        for (String each : owed) {
            if (each.startsWith("Active ×") || each.startsWith("Locked ×")) {
                out.add(each);
            }
        }
        return out;
    }

    /** An order on the cases is a line, and the way past it reads the account nowhere. */
    @Test
    void anOrderOnTheCasesStillDrawsItsLine() {
        Measured below = measured(AS_DECLARED, "let apply (account, reason) =\n"
                + "    if reason < Expired then lock(account) else account\n");
        assertEquals(OWED_BY_THE_MATCH, below.owed());
        assertFalse(below.borders().isEmpty(), "a `<` asks the order, and the line is on it");
    }

    /**
     * A case written with nothing in it, compared with a value of a sum whose other cases carry
     * something, is the same question: no order counts those cases, and the value is the case or
     * it is not.
     */
    @Test
    void aSumWhoseOtherCasesCarrySomethingIsReadTheSameWay() {
        String carrying = "WrongPassword | Expired | Closed";
        String rows = "Closed { note = \"x\" }";
        Measured equality = measured(carrying, "let apply (account, reason) =\n"
                + "    if reason == WrongPassword then lock(account) else account\n",
                "data Closed\n", "data Closed = { note: String }\n", rows);
        Measured match = measured(carrying, MATCH, "data Closed\n",
                "data Closed = { note: String }\n", rows);
        assertEquals(OWED_BY_THE_MATCH, match.owed());
        assertEquals(match.owed(), equality.owed());
        assertEquals(List.of(), equality.borders());
    }

    /**
     * How many elements of an input list are a case is a number of the input, and a comparison of
     * it draws a line on it: the case compared with each element is which case that element is,
     * and how many of them are is counted on the list.
     */
    @Test
    void aCountOfTheElementsThatAreACaseKeepsItsLine() {
        Compilation compilation = Compilation.ofSource("""
                module probe.count

                data WrongPassword
                data Expired
                data Closed
                data Reason = WrongPassword | Expired | Closed

                behavior once : (xs: List<Reason>) -> Bool

                let once (xs) = List.length(List.filter(x -> x == Expired, xs)) == 1

                example once
                    | ([]) -> false
                    | ([Expired]) -> true
                    | ([Expired, Expired]) -> false
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList());
        assertEquals(List.of("once/#xs [xs[*] is Expired]"),
                new Measured(compilation, null).borders(),
                "a line on how many are Expired, and none on the order of the cases at an element");
    }

    private record Measured(Compilation compilation, PartitionEvidence evidence) {

        Set<String> owed() {
            Set<String> out = new LinkedHashSet<>();
            for (PartitionEvidence.PairSpace.AxisPair pair : evidence.pairs().space()) {
                PartitionEvidence.PairSpace.Owed.Listed listed = assertInstanceOf(
                        PartitionEvidence.PairSpace.Owed.Listed.class, pair.owed());
                for (PartitionEvidence.PairSpace.Cell cell : listed.cells()) {
                    out.add(cell.one() + " × " + cell.other());
                }
            }
            return out;
        }

        List<String> pairGaps() {
            return AdequacyReport.of(compilation).adequacyGaps().stream()
                    .filter(each -> each.kind() == Adequacy.Kind.PAIR_UNCOVERED)
                    .map(each -> each.about().toString())
                    .toList();
        }

        /** The axis of every border the document says is drawn. */
        List<String> borders() {
            JsonNode document = JSON.readTree(AdequacyReport.of(compilation)
                    .json(SourceRendering.namedByIdentity(compilation.texts())));
            List<String> out = new ArrayList<>();
            collect(document, out);
            return out;
        }

        private static void collect(JsonNode node, List<String> out) {
            if (node.isObject() && node.has("besides")) {
                out.add(node.path("axis").asString());
            }
            for (JsonNode child : node) {
                collect(child, out);
            }
        }
    }

    private static Measured measured(String cases, String body) {
        return measured(cases, body, "", "", "Closed");
    }

    private static Measured measured(String cases, String body, String declared,
                                     String declaredAs, String lastReason) {
        String head = DECLARATIONS.formatted(cases);
        return measuredSource((declared.isEmpty() ? head : head.replace(declared, declaredAs))
                + body + ROWS.formatted(lastReason));
    }

    private static Measured measuredSource(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(each -> each.diagnostic().code() + " " + each.diagnostic().said())
                        .toList(),
                "the model under test compiles and its rows hold");
        Map<String, PartitionEvidence> all = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value();
        assertNotNull(all, "the model under test is measured");
        assertTrue(all.containsKey("apply"));
        return new Measured(compilation, all.get("apply"));
    }
}
