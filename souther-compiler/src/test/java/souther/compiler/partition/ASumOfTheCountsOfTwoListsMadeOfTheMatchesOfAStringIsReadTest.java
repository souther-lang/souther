package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.query.Output;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A guard on the sum of how many accounts a lead's address reaches and how many contacts it does
 * is read as each of the two counts is read alone: the address is parted by what the pieces of the
 * account domains can hold and by what the contacts' addresses can hold, each by its own partner.
 *
 * <p>What the sum adds to a count read alone is the other count's statement beside it. It asks no
 * contact to be the lead's address where the account count decides, which a book of no contact
 * meets whatever the address is. And the address is related to two other values, a domain of an
 * account and an address of a contact: the first parts it by the pieces it can be, the second
 * leaves it undivided, and the two do not contradict one another.
 */
class ASumOfTheCountsOfTwoListsMadeOfTheMatchesOfAStringIsReadTest {

    private static final String BOOKS = """
            module demo

            data AccountId = String
                invariant String.matches("001[0-9A-Za-z]{12}", value)
            data ContactId = String
                invariant String.matches("003[0-9A-Za-z]{12}", value)
            data EmailAddress = String
                invariant String.matches("[^@\\\\s]+@[^@\\\\s]+\\\\.[^@\\\\s]+", value)
            data PhoneNumber = String
                invariant String.matches("\\\\+?[0-9][0-9 \\\\-()]{6,19}", value)
            data DomainName = String
                invariant String.matches("[a-z0-9]([a-z0-9\\\\-]*[a-z0-9])?(\\\\.[a-z0-9]([a-z0-9\\\\-]*[a-z0-9])?)+", value)

            data EmailOnly     = { email: EmailAddress }
            data PhoneOnly     = { phone: PhoneNumber }
            data EmailAndPhone = { email: EmailAddress, phone: PhoneNumber }
            data ContactPoint  = EmailOnly | PhoneOnly | EmailAndPhone

            data Account = { id: AccountId, domain: DomainName? }
            data Contact = { id: ContactId, reach: ContactPoint }
            data AccountBook = List<Account>
                invariant List.allDistinctBy(.id, value)
            data ContactBook = List<Contact>
                invariant List.allDistinctBy(.id, value)
            data NewLead = { reach: ContactPoint }

            data NoDuplicate = { n: Int }
            data Duplicate = { n: Int }

            let emailOf (reach: ContactPoint): List<EmailAddress> =
                match reach with
                    | EmailOnly { email }     -> [ email ]
                    | EmailAndPhone { email } -> [ email ]
                    | PhoneOnly               -> []

            let domainOf (email: EmailAddress): List<DomainName> =
                List.flatMap(d -> if DomainName(d) as name then [ name ] else [],
                             List.drop(1, String.split("@", String.lowercase(email.value))))

            let domainsOf (reach: ContactPoint): List<DomainName> =
                List.flatMap(e -> domainOf(e), emailOf(reach))

            let accountHasDomain (domain: DomainName, a: Account): Bool =
                match a.domain with
                    | Some own -> own == domain
                    | None      -> false

            let accountsOnDomain (domain: DomainName, AccountBook(rows)): List<Account> =
                List.filter(a -> accountHasDomain(domain, a), rows)

            let domainMatches (reach: ContactPoint, accounts: AccountBook): List<Account> =
                List.flatMap(d -> accountsOnDomain(d, accounts), domainsOf(reach))

            let reachHasEmail (email: EmailAddress, reach: ContactPoint): Bool =
                match reach with
                    | EmailOnly { email = own }     -> own == email
                    | EmailAndPhone { email = own } -> own == email
                    | PhoneOnly                     -> false

            let contactsOnEmail (email: EmailAddress, ContactBook(rows)): List<Contact> =
                List.filter(c -> reachHasEmail(email, c.reach), rows)

            let emailMatches (reach: ContactPoint, contacts: ContactBook): List<Contact> =
                List.flatMap(e -> contactsOnEmail(e, contacts), emailOf(reach))

            behavior screen : (lead: NewLead, accounts: AccountBook, contacts: ContactBook)
                    -> NoDuplicate | Duplicate
                constructs Duplicate, DomainName, NoDuplicate

            let screen (lead, accounts, contacts) = {
                let matchedAccounts = List.map(a -> a.id, domainMatches(lead.reach, accounts))
                let matchedContacts = List.map(c -> c.id, emailMatches(lead.reach, contacts))
                guard GUARD else NoDuplicate { n = 0 }
                Duplicate { n = 1 }
            }
            """;

    private static final String THE_SUM =
            "List.length(matchedAccounts) + List.length(matchedContacts) >= 1";

    private static String source(String guard) {
        return BOOKS.replace("GUARD", guard);
    }

    private static String json(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        return AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }

    @Test
    void theSumIsReadAsEachCountAloneIs() {
        for (String guard : List.of("List.length(matchedAccounts) >= 1",
                "List.length(matchedContacts) >= 1", THE_SUM)) {
            String report = json(source(guard));
            assertTrue(report.contains("relation_shown_over_a_region"), () -> guard + report);
            assertFalse(report.contains("relation_not_shown_to_reach_every_value"),
                    () -> guard + report);
        }
    }

    /**
     * The rows offered for the classes of the lead's address are run, and between them the guard
     * comes out both ways.
     */
    @Test
    void theRowsOfferedForTheSumReachBothSidesOfTheGuard() {
        String model = source(THE_SUM);
        Compilation offering = Compilation.ofSource(model, "Main");
        offering.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(offering);
        String block = GeneratedRows.of(
                Adequacy.offeredFor(offering.db(), OfferingRequest.overTheModule("demo")),
                Map.of(), SourceRendering.namedByIdentity(offering.texts()),
                offering.db()).textInEnglish();
        // Every line of the block but its comments is a row, wrapped onto as many as it takes.
        String examples = block.lines().dropWhile(line -> !line.startsWith("example "))
                .skip(1).filter(line -> !line.startsWith("//"))
                .collect(Collectors.joining("\n"))
                .replace("<?>", "NoDuplicate { n = 0 }");
        assertFalse(examples.isBlank(), block);
        Compilation running = Compilation.ofSource(model + "\nexample screen\n" + examples + "\n",
                "Main");
        // A row expecting NoDuplicate does not hold where the guard comes out the other way, which
        // is all that is wrong with any of them.
        ACompiledModel.refusedWith(List.of("E1905", "E1905", "E1905"), running);
        Output.Examples key = Output.Examples.asked(running.db(), "demo",
                running.sourceIds().get(0));
        Set<String> answered = running.db().ask(key).value().rows().stream()
                .map(row -> row.resultArm().name()).collect(Collectors.toSet());
        assertEquals(Set.of("NoDuplicate", "Duplicate"), answered, examples);
    }
}
