package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A guard holding a sum of the counts of lists made by a flatMap of an attempt on the pieces of a
 * string against a bound is read as whether some one of the lists holds something, where the bound
 * parts nought from every sum above it, and as the relation it is otherwise.
 */
class ASumOfTheCountsOfListsMadeByFlatMapOfAnAttemptIsReadTest {

    private static final String GUARD = "List.length(matchedAccounts) + List.length(matchedContacts) >= 1";

    private static final String TWO_BOOKS = """
            module probe.s2 exposing ( screen, Email, Domain, Account, Contact, Book, Roll,
                                       Found, Nobody )

            data Email = String
                invariant String.matches("[^@\\\\s]+@[^@\\\\s]+\\\\.[^@\\\\s]+", value)

            data Domain = String
                invariant String.matches("[a-z0-9]+(\\\\.[a-z0-9]+)+", value)

            data Account = { domain: Domain }
            data Contact = { domain: Domain }
            data Book = List<Account>
            data Roll = List<Contact>

            data Found
            data Nobody

            behavior screen : (lead: Email, accounts: Book, contacts: Roll) -> Found | Nobody
                constructs Domain

            let domainOf (email: Email): List<Domain> =
                List.flatMap(d -> if Domain(d) as name then [ name ] else [],
                             List.drop(1, String.split("@", String.lowercase(email.value))))

            let accountsOn (domain: Domain, Book(rows)): List<Account> =
                List.filter(a -> a.domain == domain, rows)

            let contactsOn (domain: Domain, Roll(rows)): List<Contact> =
                List.filter(c -> c.domain == domain, rows)

            let screen (lead, accounts, contacts) = {
                let matchedAccounts = List.flatMap(d -> accountsOn(d, accounts), domainOf(lead))
                let matchedContacts = List.flatMap(d -> contactsOn(d, contacts), domainOf(lead))
                %s
                Found
            }

            example screen
                | "an account" : (Email("a@x.jp"), Book([ Account { domain = Domain("x.jp") } ]),
                                  Roll([ ])) -> @ACCOUNT@
                | "a contact" : (Email("a@x.jp"), Book([ ]),
                                 Roll([ Contact { domain = Domain("x.jp") } ])) -> @CONTACT@
                | "both" : (Email("a@x.jp"), Book([ Account { domain = Domain("x.jp") } ]),
                            Roll([ Contact { domain = Domain("x.jp") } ])) -> @BOTH@                | "neither" : (Email("a@x.jp"), Book([ Account { domain = Domain("y.jp") } ]),
                               Roll([ Contact { domain = Domain("y.jp") } ])) -> Nobody
                | "empty" : (Email("a@x.jp"), Book([ ]), Roll([ ])) -> Nobody
                | "unbuilt" : (Email("a@x_y.jp"), Book([ Account { domain = Domain("x.jp") } ]),
                               Roll([ ])) -> Nobody
            """;

    private static String report(String guard) {
        return report(guard, "Found", "Found", "Found");
    }

    /** The model with {@code guard}, and what each of the three rows with a match comes to. */
    private static String report(String guard, String account, String contact, String both) {
        return reportOf("guard " + guard + " else Nobody", account, contact, both);
    }

    /** The model with {@code statements} before the answer, in a block of the behavior. */
    private static String reportOf(String statements) {
        return reportOf(statements, "Found", "Found", "Found");
    }

    private static String reportOf(String statements, String account, String contact,
                                   String both) {
        Compilation compilation = Compilation.ofSource(TWO_BOOKS.formatted(statements)
                .replace("@ACCOUNT@", account).replace("@CONTACT@", contact)
                .replace("@BOTH@", both), "Main");
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

    private static List<String> aboutAValueMadeFromAnother(String report) {
        return notRead(report).stream()
                .filter(line -> line.contains("a value made from this one")).toList();
    }

    /**
     * The sum held at least one is some account or some contact existing, and neither it nor the
     * fork over it is left as a rule about a value made from the lead.
     */
    @Test
    void aSumOfCountsAtLeastOneIsSomeOneOfTheListsHoldingSomething() {
        String report = report(GUARD);
        assertEquals(List.of(), aboutAValueMadeFromAnother(report), report);
        assertTrue(notRead(report).stream().noneMatch(line -> line.contains("fork@")), report);
    }

    /** No example is dropped, merged or left waiting for the reading. */
    @Test
    void theExamplesAreAllOwedAndMet() {
        String report = report(GUARD);
        List<String> owed = report.lines().map(line -> line.strip().replaceAll("\\s+", " "))
                .toList();
        assertTrue(owed.contains("screen implemented rows 6 pending 0"), report);
        assertTrue(owed.stream().anyMatch(line -> line.matches("branch ([1-9]\\d*)/\\1")), report);
        assertTrue(owed.contains("decision rules 2 taken 2"), report);
    }

    /** Held above nought, a sum is none of them holding something, or some one of them. */
    @Test
    void theOtherSpellingsOfWhetherAnyHoldsSomethingAreReadAlike() {
        for (String guard : List.of(
                "List.length(matchedAccounts) + List.length(matchedContacts) > 0",
                "List.length(matchedAccounts) + List.length(matchedContacts) /= 0",
                "Bool.not(List.length(matchedAccounts) + List.length(matchedContacts) == 0)")) {
            assertEquals(List.of(), aboutAValueMadeFromAnother(report(guard)), guard);
        }
    }

    /**
     * A sum or a size given a name is the check as much as one written in the guard: the name
     * stands for what it is bound to wherever the guard reads it.
     */
    @Test
    void aSumGivenANameIsTheCheckToo() {
        String sum = """
                let total = List.length(matchedAccounts) + List.length(matchedContacts)
                guard total >= 1 else Nobody""";
        assertEquals(List.of(), aboutAValueMadeFromAnother(reportOf(sum)), sum);
    }

    @Test
    void aSizeGivenANameIsTheCheckToo() {
        String size = """
                let accounts = List.length(matchedAccounts)
                guard accounts >= 1 || List.length(matchedContacts) >= 1 else Nobody""";
        assertEquals(List.of(), aboutAValueMadeFromAnother(reportOf(size)), size);
    }

    /**
     * A sum that says how many, and a difference of counts, are not whether some one of the lists
     * holds something, and stay as unread as they were: a value not shown to be made stays not
     * shown.
     */
    @Test
    void aBoundThatSaysHowManyAndADifferenceAreNotReadAsExistence() {
        String atLeastTwo = "List.length(matchedAccounts) + List.length(matchedContacts) >= 2";
        assertFalse(aboutAValueMadeFromAnother(report(atLeastTwo, "Nobody", "Nobody", "Found"))
                .isEmpty(), atLeastTwo);
        String difference = "List.length(matchedAccounts) - List.length(matchedContacts) >= 1";
        assertFalse(aboutAValueMadeFromAnother(report(difference, "Found", "Nobody", "Nobody"))
                .isEmpty(), difference);
    }

    /** A list mapped over the lists another made is held somewhere as the list it maps is. */
    @Test
    void aListMappedOverTheListsAFlatMapMadeIsReadLikeThoseLists() {
        String mapped = """
                let named = List.map(a -> a.domain, matchedAccounts)
                guard List.length(named) + List.length(matchedContacts) >= 1 else Nobody""";
        String report = reportOf(mapped);
        assertEquals(List.of(), aboutAValueMadeFromAnother(report), report);
    }

    /** A flatMap walking the domains another flatMap made of the emails is the same existence. */
    @Test
    void aFlatMapWalkingTheListsAnotherFlatMapMadeIsReadLikeTheOneLevel() {
        String nested = """
                let domains = List.flatMap(e -> domainOf(e), [ lead ])
                let viaDomains = List.flatMap(d -> accountsOn(d, accounts), domains)
                guard List.length(viaDomains) + List.length(matchedContacts) >= 1 else Nobody""";
        String report = reportOf(nested);
        assertEquals(List.of(), aboutAValueMadeFromAnother(report), report);
    }

    private static final String PLAIN_COUNT = """
            module probe.s0 exposing ( screen, Domain, Yes, No )

            data Domain = String
                invariant String.matches("[a-z0-9]+(\\\\.[a-z0-9]+)+", value)

            data Yes
            data No

            behavior screen : (s: String) -> Yes | No
                constructs Domain

            let domainsIn (s: String): List<Domain> =
                List.flatMap(d -> if Domain(d) as name then [ name ] else [],
                             List.drop(1, String.split("@", s)))

            let screen (s) = {
                let a = domainsIn(s)
                guard List.length(a) >= 1 else No
                Yes
            }

            example screen
                | "found" : ("a@x.jp") -> Yes
                | "none" : ("a@X") -> No
            """;

    /**
     * What the strings the list holds something for divide of the input is not worked out, and the
     * report does not say it is: the fork over the count stays a rule nothing read, at the string
     * it is about, and the measurement is partial.
     */
    @Test
    void theStringsAListOfPiecesHoldsSomethingForAreNotReportedAsDividingNothing() {
        Compilation compilation = Compilation.ofSource(PLAIN_COUNT, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        assertTrue(notRead(report).stream().anyMatch(line -> line.contains("fork@")), report);
        assertTrue(report.contains("measurement: partial"), report);
    }
}
