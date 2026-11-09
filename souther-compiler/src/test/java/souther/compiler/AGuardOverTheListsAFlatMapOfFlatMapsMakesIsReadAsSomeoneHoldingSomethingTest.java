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
 * A guard over the count of the lists a flatMap made walking the lists another flatMap made, down
 * to the pieces of a string an attempt built values of, is read as whether some element of the
 * lists written out holds one that meets what the closures keep it by. The lists the outer flatMap
 * walks are written out, one application of its closure for each element, and each application
 * is read as the one-level case is.
 */
class AGuardOverTheListsAFlatMapOfFlatMapsMakesIsReadAsSomeoneHoldingSomethingTest {

    /**
     * The shape of a lead's reach and an account's optional domain the example models have: the
     * address is taken out of the case the reach is, and the domain of an account is compared
     * once it is there.
     */
    private static final String ACCOUNTS_OF_A_REACH = """
            module probe.s3 exposing ( screen, Email, Phone, Domain, EmailOnly, PhoneOnly,
                                       EmailAndPhone, Reach, Lead, Account, Book, Found, Nobody )

            data Email = String
                invariant String.matches("[^@\\\\s]+@[^@\\\\s]+\\\\.[^@\\\\s]+", value)

            data Phone = String
                invariant String.matches("[0-9]{7,12}", value)

            data Domain = String
                invariant String.matches("[a-z0-9]+(\\\\.[a-z0-9]+)+", value)

            data EmailOnly = { email: Email }
            data PhoneOnly = { phone: Phone }
            data EmailAndPhone = { email: Email, phone: Phone }
            data Reach = EmailOnly | PhoneOnly | EmailAndPhone
            data Lead = { reach: Reach }
            data Account = { domain: Domain? }
            data Book = List<Account>

            data Found
            data Nobody

            behavior screen : (lead: Lead, accounts: Book) -> Found | Nobody
                constructs Domain

            let emailOf (reach: Reach): List<Email> =
                match reach with
                    | EmailOnly { email }     -> [ email ]
                    | EmailAndPhone { email } -> [ email ]
                    | PhoneOnly               -> []

            let domainOf (email: Email): List<Domain> =
                List.flatMap(d -> if Domain(d) as name then [ name ] else [],
                             List.drop(1, String.split("@", String.lowercase(email.value))))

            let domainsOf (reach: Reach): List<Domain> =
                List.flatMap(e -> domainOf(e), emailOf(reach))

            let accountHasDomain (domain: Domain, a: Account): Bool =
                match a.domain with
                    | Some own -> own == domain
                    | None     -> false

            let accountsOnDomain (domain: Domain, Book(rows)): List<Account> =
                List.filter(a -> accountHasDomain(domain, a), rows)

            let domainMatches (reach: Reach, accounts: Book): List<Account> =
                List.flatMap(d -> accountsOnDomain(d, accounts), domainsOf(reach))

            let screen (lead, accounts) = {
                let matched = domainMatches(lead.reach, accounts)
                guard %s else Nobody
                Found
            }

            example screen
                | "an account on the domain" :
                    (Lead { reach = EmailOnly { email = Email("a@x.jp") } },
                     Book([ Account { domain = Domain("x.jp") } ])) -> @ONE@
                | "on the other case that has an address" :
                    (Lead { reach = EmailAndPhone { email = Email("a@x.jp"),
                                                    phone = Phone("0312345678") } },
                     Book([ Account { domain = Domain("x.jp") } ])) -> @ONE@
                | "two accounts on the domain" :
                    (Lead { reach = EmailOnly { email = Email("a@x.jp") } },
                     Book([ Account { domain = Domain("x.jp") },
                            Account { domain = Domain("x.jp") } ])) -> Found
                | "none on the domain" :
                    (Lead { reach = EmailOnly { email = Email("a@x.jp") } },
                     Book([ Account { domain = Domain("y.jp") } ])) -> Nobody
                | "no website on file" :
                    (Lead { reach = EmailOnly { email = Email("a@x.jp") } },
                     Book([ Account { domain = None } ])) -> Nobody
                | "no address" :
                    (Lead { reach = PhoneOnly { phone = Phone("0312345678") } },
                     Book([ Account { domain = Domain("x.jp") } ])) -> Nobody
                | "no accounts" :
                    (Lead { reach = EmailOnly { email = Email("a@x.jp") } }, Book([ ])) -> Nobody
                | "a domain that is no domain name" :
                    (Lead { reach = EmailOnly { email = Email("a@x_y.jp") } },
                     Book([ Account { domain = Domain("x.jp") } ])) -> Nobody
            """;

    /**
     * Two addresses written out, each with its own pieces: an account on either one's domain is a
     * match, and an account on neither is not.
     */
    private static final String ACCOUNTS_OF_TWO_ADDRESSES = """
            module probe.s4 exposing ( screen, Email, Domain, Pair, Account, Book, Found, Nobody )

            data Email = String
                invariant String.matches("[^@\\\\s]+@[^@\\\\s]+\\\\.[^@\\\\s]+", value)

            data Domain = String
                invariant String.matches("[a-z0-9]+(\\\\.[a-z0-9]+)+", value)

            data Pair = { first: Email, second: Email }
            data Account = { domain: Domain? }
            data Book = List<Account>

            data Found
            data Nobody

            behavior screen : (pair: Pair, accounts: Book) -> Found | Nobody
                constructs Domain

            let domainOf (email: Email): List<Domain> =
                List.flatMap(d -> if Domain(d) as name then [ name ] else [],
                             List.drop(1, String.split("@", String.lowercase(email.value))))

            let accountHasDomain (domain: Domain, a: Account): Bool =
                match a.domain with
                    | Some own -> own == domain
                    | None     -> false

            let accountsOn (domain: Domain, Book(rows)): List<Account> =
                List.filter(a -> accountHasDomain(domain, a), rows)

            let screen (pair, accounts) = {
                let domains = List.flatMap(e -> domainOf(e), [ pair.first, pair.second ])
                let matched = List.flatMap(d -> accountsOn(d, accounts), domains)
                guard List.length(matched) >= 1 else Nobody
                Found
            }

            example screen
                | "on the first" : (Pair { first = Email("a@x.jp"), second = Email("b@y.jp") },
                                    Book([ Account { domain = Domain("x.jp") } ])) -> Found
                | "on the second" : (Pair { first = Email("a@x.jp"), second = Email("b@y.jp") },
                                     Book([ Account { domain = Domain("y.jp") } ])) -> Found
                | "on the second behind one with no website and one on neither" :
                    (Pair { first = Email("a@x.jp"), second = Email("b@y.jp") },
                     Book([ Account { domain = None }, Account { domain = Domain("z.jp") },
                            Account { domain = Domain("y.jp") } ])) -> Found
                | "on neither" : (Pair { first = Email("a@x.jp"), second = Email("b@y.jp") },
                                  Book([ Account { domain = Domain("z.jp") } ])) -> Nobody
                | "no website on file" : (Pair { first = Email("a@x.jp"), second = Email("b@y.jp") },
                                          Book([ Account { domain = None } ])) -> Nobody
                | "none" : (Pair { first = Email("a@x.jp"), second = Email("b@y.jp") },
                            Book([ ])) -> Nobody
            """;

    private static String report(String model, String guard, String one) {
        Compilation compilation = Compilation.ofSource(
                model.formatted(guard).replace("@ONE@", one), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static List<String> aboutAValueMadeFromAnother(String report) {
        return report.lines().filter(line -> line.contains("a value made from this one")).toList();
    }

    /**
     * The guard is read, no rule of it is left about a value made from the lead, and no example
     * is dropped, merged or left waiting for the reading.
     */
    @Test
    void aCountAtLeastOneIsSomeElementOfSomeListHoldingOneAndEveryExampleIsMet() {
        String report = report(ACCOUNTS_OF_A_REACH, "List.length(matched) >= 1", "Found");
        assertEquals(List.of(), aboutAValueMadeFromAnother(report), report);
        List<String> owed = report.lines().map(line -> line.strip().replaceAll("\\s+", " "))
                .toList();
        assertTrue(owed.contains("screen implemented rows 8 pending 0"), report);
        assertTrue(owed.stream().anyMatch(line -> line.matches("branch ([1-9]\\d*)/\\1")), report);
        assertTrue(owed.contains("decision rules 2 taken 2"), report);
    }

    /** How many are on the domain is the count and not whether there is one. */
    @Test
    void aCountOfTwoOrMoreIsNotReadAsSomeoneHoldingOne() {
        String report = report(ACCOUNTS_OF_A_REACH, "List.length(matched) >= 2", "Nobody");
        assertFalse(aboutAValueMadeFromAnother(report).isEmpty(), report);
    }

    /**
     * Each address is read with its own pieces: an account on either domain is a match, and the
     * examples all hold, one of them for the second address alone.
     */
    @Test
    void eachWrittenOutAddressIsReadWithItsOwnPieces() {
        String report = report(ACCOUNTS_OF_TWO_ADDRESSES, "unused", "unused");
        assertEquals(List.of(), aboutAValueMadeFromAnother(report), report);
        List<String> owed = report.lines().map(line -> line.strip().replaceAll("\\s+", " "))
                .toList();
        assertTrue(owed.contains("screen implemented rows 6 pending 0"), report);
        assertTrue(report.contains("pair.second"), report);
        assertTrue(report.contains("pair.first"), report);
    }

    private static final String EVERY_DOMAIN_HAS_AN_ACCOUNT =
            "guard List.all(d -> List.length(accountsOn(d, accounts)) >= 1, domains) else Nobody";

    private static final String SOME_DOMAIN_HAS_AN_ACCOUNT =
            "guard List.any(d -> List.length(accountsOn(d, accounts)) >= 1, domains) else Nobody";

    /**
     * The same lists asked whether every one of the domains has an account, and whether some one
     * does. Every one is the denial of some one failing, which the law of the operation says as
     * a quantifier that does not hold, and the reading met under it is the same one: the report is
     * made, and the examples, one of them for both domains, are all met.
     */
    @Test
    void theLawOfAnOperationThatAsksEveryElementIsReadOfTheSameLists() {
        String guarded = "    let matched = List.flatMap(d -> accountsOn(d, accounts), domains)\n"
                + "    guard List.length(matched) >= 1 else Nobody";
        assertTrue(ACCOUNTS_OF_TWO_ADDRESSES.contains(guarded));
        String base = ACCOUNTS_OF_TWO_ADDRESSES.replace(guarded, "    %s");
        String some = report(base.replace("%s", SOME_DOMAIN_HAS_AN_ACCOUNT), "", "");
        assertTrue(some.lines().map(line -> line.strip().replaceAll("\\s+", " ")).toList()
                .contains("screen implemented rows 6 pending 0"), some);
        String everyone = base.replace("])) -> Found", "])) -> Nobody").replace(
                "| \"none\" :", "| \"on both\" : (Pair { first = Email(\"a@x.jp\"),"
                        + " second = Email(\"b@y.jp\") }, Book([ Account { domain = Domain(\"x.jp\") },"
                        + " Account { domain = Domain(\"y.jp\") } ])) -> Found\n"
                        + "                | \"none\" :");
        String all = report(everyone.replace("%s", EVERY_DOMAIN_HAS_AN_ACCOUNT), "", "");
        assertTrue(all.lines().map(line -> line.strip().replaceAll("\\s+", " ")).toList()
                .contains("screen implemented rows 7 pending 0"), all);
    }

    private static final String ACCOUNTS_THAT_MAY_STOP = """
            module probe.s5 exposing ( screen, Email, Domain, Pair, Account, Book, Found, Nobody )

            data Email = String
                invariant String.matches("[^@\\\\s]+@[^@\\\\s]+\\\\.[^@\\\\s]+", value)

            data Domain = String
                invariant String.matches("[a-z0-9]+(\\\\.[a-z0-9]+)+", value)

            data Pair = { first: Email, second: Email }
            data Account = { domain: Domain }
            data Book = List<Account>

            data Found
            data Nobody

            behavior screen : (pair: Pair, accounts: Book) -> Found | Nobody
                constructs Domain

            let domainOf (email: Email): List<Domain> =
                List.flatMap(d -> if Domain(d) as name then [ name ] else [],
                             List.drop(1, String.split("@", String.lowercase(email.value))))

            let accountsOn (domain: Domain, Book(rows)): List<Account> =
                List.filter(a -> a.domain == domain, rows)

            let sizeOf (Book(rows)): Int = List.length(rows)

            let screen (pair, accounts) = {
                let domains = List.flatMap(e -> domainOf(e), [ pair.first, pair.second ])
                let matched = List.flatMap(
                    d -> if 100 / sizeOf(accounts) >= 1 then accountsOn(d, accounts) else [],
                    domains)
                guard List.length(matched) >= 1 else Nobody
                Found
            }

            example screen
                | "on the first" : (Pair { first = Email("a@x.jp"), second = Email("b@y.jp") },
                                    Book([ Account { domain = Domain("x.jp") } ])) -> Found
                | "on neither" : (Pair { first = Email("a@x.jp"), second = Email("b@y.jp") },
                                  Book([ Account { domain = Domain("z.jp") } ])) -> Nobody
            """;

    /**
     * Some account being on a domain is true once the first is found, but the lists are all made
     * and the closure divides by the number of accounts, so a run may stop on the way whichever
     * address the account is on. What is read is the element being one of the pieces, and a
     * closure that is a choice with a division in it is none of that: the guard stays unread and
     * the measurement is not complete, so a stop is not carried off by the first match.
     */
    @Test
    void aClosureThatMayStopIsNotReadAsSomeAccountBeingFound() {
        String report = report(ACCOUNTS_THAT_MAY_STOP, "unused", "unused");
        assertFalse(aboutAValueMadeFromAnother(report).isEmpty(), report);
        assertTrue(report.contains("measurement: partial"), report);
    }
}
