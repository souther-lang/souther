package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule over a list made by a flatMap of an attempt on the pieces of a lowercased string is read.
 */
class AListMadeByFlatMapOfAnAttemptOnADerivedStringIsReadTest {

    private static final String SCREEN = """
            module probe.p2 exposing ( screen, Email, Domain, Account, Book, Found, Nobody )

            data Email = String
                invariant String.matches("[^@\\\\s]+@[^@\\\\s]+\\\\.[^@\\\\s]+", value)

            data Domain = String
                invariant String.matches("[a-z0-9]+(\\\\.[a-z0-9]+)+", value)

            data Account = { domain: Domain }
            data Book = List<Account>

            data Found
            data Nobody

            behavior screen : (lead: Email, accounts: Book) -> Found | Nobody
                constructs Domain

            let domainOf (email: Email): List<Domain> =
                List.flatMap(d -> if Domain(d) as name then [ name ] else [],
                             List.drop(1, String.split("@", String.lowercase(email.value))))

            let onDomain (domain: Domain, a: Account): Bool = a.domain == domain

            let screen (lead, Book(rows)) =
                if List.length(List.flatMap(d -> List.filter(a -> onDomain(d, a), rows),
                                            domainOf(lead))) >= 1
                then Found else Nobody

            example screen
                | "found" : (Email("a@x.jp"), Book([ Account { domain = Domain("x.jp") } ])) -> Found
                | "none" : (Email("a@x.jp"), Book([ Account { domain = Domain("y.jp") } ])) -> Nobody
                | "empty" : (Email("a@x.jp"), Book([ ])) -> Nobody
                | "unbuilt" : (Email("a@x_y.jp"), Book([ Account { domain = Domain("x.jp") } ])) -> Nobody
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

    private static final String COUNT = """
            module probe.p1 exposing ( count, Domain, Yes, No )

            data Domain = String
                invariant String.matches("[a-z0-9]+(\\\\.[a-z0-9]+)+", value)

            data Yes
            data No

            behavior count : (xs: List<String>) -> Yes | No
                constructs Domain

            let count (xs) =
                if List.length(List.flatMap(d -> if Domain(d) as name then [ name ] else [], xs)) >= 1
                then Yes else No

            example count
                | "one" : (["x.jp"]) -> Yes
                | "none" : (["X"]) -> No
                | "empty" : ([ ]) -> No
            """;

    private static final String PLAIN = """
            module probe.p0 exposing ( pick, Yes, No )

            data Yes
            data No

            behavior pick : (s: String) -> Yes | No

            let pick (s) = if String.matches("[a-z]+", s) then Yes else No

            example pick
                | "in" : ("x") -> Yes
                | "out" : ("X") -> No
            """;

    private static final String ATTEMPT_ON_POSITION = """
            module probe.p0b exposing ( pick, Domain, Yes, No )

            data Domain = String
                invariant String.matches("[a-z]+", value)

            data Yes
            data No

            behavior pick : (s: String) -> Yes | No
                constructs Domain

            let pick (s) = if Domain(s) as d then Yes else No

            example pick
                | "in" : ("x") -> Yes
                | "out" : ("X") -> No
            """;

    @Test
    void aMatchesOnAnInputStringIsRead() {
        String report = report(PLAIN);
        assertEquals(List.of(), notRead(report));
    }

    @Test
    void anAttemptOnAnInputStringIsRead() {
        String report = report(ATTEMPT_ON_POSITION);
        assertEquals(List.of(), notRead(report));
    }

    private static final String FILTERED = """
            module probe.p1b exposing ( count, Yes, No )

            data Yes
            data No

            behavior count : (xs: List<String>) -> Yes | No

            let count (xs) =
                if List.length(List.filter(d -> String.matches("[a-z0-9]+(\\\\.[a-z0-9]+)+", d), xs)) >= 1
                then Yes else No

            example count
                | "one" : (["x.jp"]) -> Yes
                | "none" : (["X"]) -> No
                | "empty" : ([ ]) -> No
            """;

    private static final String ANY = """
            module probe.p1c exposing ( count, Yes, No )

            data Yes
            data No

            behavior count : (xs: List<String>) -> Yes | No

            let count (xs) =
                if List.any(d -> String.matches("[a-z0-9]+(\\\\.[a-z0-9]+)+", d), xs)
                then Yes else No

            example count
                | "one" : (["x.jp"]) -> Yes
                | "none" : (["X"]) -> No
                | "empty" : ([ ]) -> No
            """;

    @Test
    void aSomeOverAListAloneIsRead() {
        String report = report(ANY);
        assertEquals(List.of(), notRead(report));
    }

    @Test
    void theCountOfAFilteredListAloneIsRead() {
        String report = report(FILTERED);
        assertEquals(List.of(), notRead(report));
    }

    /**
     * Read, and none of what the examples owe is left out because of it: the three rows are
     * counted, and both ways of the attempt and both arms of the guard are taken by them.
     */
    @Test
    void theCountOfAnAttemptAloneIsRead() {
        String report = report(COUNT);
        assertEquals(List.of(), notRead(report));
        List<String> owed = report.lines().map(line -> line.strip().replaceAll("\\s+", " "))
                .toList();
        assertTrue(owed.contains("count implemented rows 3 pending 0"), report);
        assertTrue(owed.contains("branch 4/4"), report);
        assertTrue(owed.contains("decision rules 2 taken 2"), report);
    }

    /**
     * The count guard and the fork over the derived list are read: nothing is left unread for
     * being about a value made from another.
     */
    @Test
    void noUnreadOfTheIssueExampleIsAboutAValueMadeFromAnother() {
        String report = report(SCREEN);
        assertEquals(List.of(), notRead(report).stream()
                .filter(line -> line.contains("a value made from this one")).toList(), report);
        assertTrue(notRead(report).stream().noneMatch(line -> line.contains("fork@")), report);
    }

    /**
     * What is left unread is the one comparison of a domain with a row's, and only for what it is
     * not shown to reach: its classes hold the values it was shown over, and the image of the
     * lowercase conversion is not shown. A value not shown to be made stays not shown.
     */
    @Test
    void whatIsLeftOfTheIssueExampleIsTheComparisonOverTheValuesItWasShownOver() {
        String report = report(SCREEN);
        List<String> left = notRead(report);
        assertTrue(!left.isEmpty(), report);
        assertTrue(left.stream().allMatch(line -> line.contains("comparison@")), report);
        assertTrue(left.stream().allMatch(line -> line.contains(
                "its classes hold the values it was shown over")
                || line.contains("the image of String.lowercase not shown")), report);
    }

    /** No example is dropped, merged or left waiting for the reading. */
    @Test
    void theExamplesOfTheIssueExampleAreAllOwedAndMet() {
        String report = report(SCREEN);
        List<String> owed = report.lines().map(line -> line.strip().replaceAll("\\s+", " "))
                .toList();
        assertTrue(owed.contains("screen implemented rows 4 pending 0"), report);
        assertTrue(owed.contains("branch 6/6"), report);
        assertTrue(owed.contains("decision rules 2 taken 2"), report);
    }
}
