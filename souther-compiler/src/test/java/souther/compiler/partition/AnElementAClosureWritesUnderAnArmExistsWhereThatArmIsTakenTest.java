package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An element a closure writes only under one of its arms exists where that arm is taken, and a
 * statement about the element is a statement about the pieces the arm is taken for.
 *
 * <p>The list is the pieces of a string put through an attempt to build a value: the attempt that
 * builds writes the value, the attempt that does not writes nothing. A rule over the list asks
 * whether some element meets a statement, so the elements are the pieces the attempt builds a
 * value of, and a piece it does not build one of is no element — however the statement would have
 * gone for it.
 */
class AnElementAClosureWritesUnderAnArmExistsWhereThatArmIsTakenTest {

    private static final String MODEL = """
            module probe.e exposing ( screen, Domain, Account, Found, Nobody )

            data Domain = String
                invariant String.matches("[a-z0-9]+(\\\\.[a-z0-9]+)+", value)

            data Account = { domain: Domain }

            data Found
            data Nobody

            behavior screen : (lead: String, rows: List<Account>) -> Found | Nobody
                constructs Domain

            let screen (lead, rows) =
                if List.length(List.flatMap(d -> List.filter(a -> a.domain == d, rows),
                        List.flatMap(p -> if Domain(p) as name then [ name ] else [ ],
                                     List.drop(1, String.split("@", lead))))) >= 1
                then Found else Nobody

            example screen
                | "found" : ("a@x.jp", [ Account { domain = Domain("x.jp") } ]) -> Found
                | "other" : ("a@x.jp", [ Account { domain = Domain("y.jp") } ]) -> Nobody
                | "unbuilt" : ("a@X", [ Account { domain = Domain("x.jp") } ]) -> Nobody
                | "empty" : ("a@x.jp", [ ]) -> Nobody
            """;

    private static String report(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static List<String> notRead(String report) {
        return report.lines().filter(line -> line.contains("not read")
                || line.contains("not accounted for")).toList();
    }

    private static final String TWO_WRITING = MODEL
            .replace("if Domain(p) as name then [ name ] else [ ]",
                    "if Domain(p) as name then [ name ] else [ Domain(\"z.jp\") ]");

    private static final String TWO_ELEMENTS = MODEL
            .replace("if Domain(p) as name then [ name ] else [ ]",
                    "if Domain(p) as name then [ name, name ] else [ ]");

    /**
     * The count of the list is read: the strings the attempt builds a value of and the rows they
     * are compared with are told apart by the comparison, and no example is merged, left waiting
     * or reported met for it. The comparison states a relation over the strings it is shown for,
     * which is all it is read as.
     */
    @Test
    void theElementsAreThePiecesTheAttemptBuildsAValueOf() {
        String report = report(MODEL);
        assertTrue(report.contains("lead is divided by comparison@15:64"), report);
        assertTrue(report.contains("rows[*].domain is divided by comparison@15:64"), report);
        assertTrue(report.contains("rows 4    pending 0"), report);
        assertTrue(report.contains("branch      6/6"), report);
        assertTrue(report.contains("rules 2   taken 2"), report);
        assertTrue(notRead(report).stream().allMatch(line -> line.contains("comparison@15:64")),
                report);
    }

    private static final String UNDER_A_PREDICATE = """
            module probe.f exposing ( screen, Account, Found, Nobody )

            data Account = { name: String }

            data Found
            data Nobody

            behavior screen : (lead: String, rows: List<Account>) -> Found | Nobody

            let screen (lead, rows) =
                if List.length(List.flatMap(d -> List.filter(a -> a.name == d, rows),
                        List.flatMap(p -> if String.matches("[a-z]+", p) then [ p ] else [ ],
                                     List.drop(1, String.split("@", lead))))) >= 1
                then Found else Nobody

            example screen
                | "found" : ("a@x", [ Account { name = "x" } ]) -> Found
                | "other" : ("a@x", [ Account { name = "y" } ]) -> Nobody
                | "unmatched" : ("a@X", [ Account { name = "X" } ]) -> Nobody
                | "empty" : ("a@x", [ ]) -> Nobody
            """;

    /** The same rule with the statement made inside the arm, where the piece is the element. */
    private static final String IN_THE_ARM = """
            module probe.f exposing ( screen, Account, Found, Nobody )

            data Account = { name: String }

            data Found
            data Nobody

            behavior screen : (lead: String, rows: List<Account>) -> Found | Nobody

            let screen (lead, rows) =
                if List.length(List.flatMap(p -> if String.matches("[a-z]+", p)
                                                 then List.filter(a -> a.name == p, rows) else [ ],
                                            List.drop(1, String.split("@", lead)))) >= 1
                then Found else Nobody

            example screen
                | "found" : ("a@x", [ Account { name = "x" } ]) -> Found
                | "other" : ("a@x", [ Account { name = "y" } ]) -> Nobody
                | "unmatched" : ("a@X", [ Account { name = "X" } ]) -> Nobody
                | "empty" : ("a@x", [ ]) -> Nobody
            """;

    /**
     * The element exists where the arm that writes it is taken, which is stated beside the
     * statement about it: a piece out of the language the arm is taken for is no element, though
     * the row it would be compared with has the same name. So the list is read as the rule that
     * states it inside the arm is, and the two reports are the same.
     */
    @Test
    void anElementExistsWhereTheArmThatWritesItIsTakenAndNowhereElse() {
        String report = report(UNDER_A_PREDICATE);
        assertEquals(partitionOf(report(IN_THE_ARM)), partitionOf(report), report);
        assertTrue(report.contains("rows[*].name is divided by comparison@"), report);
        assertTrue(report.contains("rows 4    pending 0"), report);
    }

    /** What the report says of how the values are divided, whatever the source positions. */
    private static List<String> partitionOf(String report) {
        List<String> lines = report.lines().toList();
        int from = lines.indexOf(lines.stream().filter(line -> line.contains("partition"))
                .findFirst().orElseThrow());
        int to = lines.indexOf(lines.stream().filter(line -> line.contains("border"))
                .findFirst().orElseThrow());
        return lines.subList(from, to).stream().map(line -> line.replaceAll("@\\d+:\\d+", "@"))
                .toList();
    }

    /**
     * A closure that writes an element under two of its arms is a list whose elements exist for
     * more than the one arm taken, so it is not read as the pieces one arm is taken for.
     */
    @Test
    void aClosureWritingUnderTwoArmsIsNotReadAsTheOnesOneArmIsTakenFor() {
        String report = report(TWO_WRITING);
        assertTrue(!report.contains("divided by comparison@15:64"), report);
        assertTrue(!notRead(report).isEmpty(), report);
    }

    /** And an arm that writes more than one element is not read as one element existing. */
    @Test
    void anArmWritingTwoElementsIsNotReadAsOneElementExisting() {
        String report = report(TWO_ELEMENTS);
        assertTrue(!report.contains("divided by comparison@15:64"), report);
        assertTrue(!notRead(report).isEmpty(), report);
    }
}
