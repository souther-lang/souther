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

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
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
            data ContactId = String
            data EmailAddress = String
                invariant String.matches("[^@\\\\s]+@[^@\\\\s]+\\\\.[^@\\\\s]+", value)
            data PhoneNumber = String
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
            """;

    /** A behavior screening a lead by {@code GUARD}, named {@code NAME}. */
    private static final String SCREEN = """

            behavior NAME : (lead: NewLead, accounts: AccountBook, contacts: ContactBook)
                    -> NoDuplicate | Duplicate
                constructs Duplicate, DomainName, NoDuplicate

            let NAME (lead, accounts, contacts) = {
                let matchedAccounts = List.map(a -> a.id, domainMatches(lead.reach, accounts))
                let matchedContacts = List.map(c -> c.id, emailMatches(lead.reach, contacts))
                guard GUARD else NoDuplicate { n = 0 }
                Duplicate { n = 1 }
            }
            """;

    private static final String THE_SUM =
            "List.length(matchedAccounts) + List.length(matchedContacts) >= 1";

    /** Each count alone and the sum, by the behavior screening by it. */
    private static final Map<String, String> GUARDS = Map.of(
            "byAccounts", "List.length(matchedAccounts) >= 1",
            "byContacts", "List.length(matchedContacts) >= 1",
            "bySum", THE_SUM);

    private static String screening(String name, String guard) {
        return SCREEN.replace("NAME", name).replace("GUARD", guard);
    }

    private static String source(String guard) {
        return BOOKS + screening("screen", guard);
    }

    /**
     * What the model's own rules draw for each behavior, measured at {@code OFF}: which relations
     * are shown over the address and where a run stops are read without running a row. The
     * guards are behaviors of one module, so the declarations they share are checked once, and
     * each behavior's part of the report is read apart from the others'.
     */
    private static Map<String, String> reportsOfEachGuard() {
        StringBuilder source = new StringBuilder(BOOKS);
        GUARDS.forEach((name, guard) -> source.append(screening(name, guard)));
        Compilation compilation = Compilation.ofSource(source.toString(), "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.OFF));
        ACompiledModel.compiles(compilation);
        JsonNode report = JsonMapper.builder().build().readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
        Map<String, String> each = new TreeMap<>();
        for (JsonNode behavior : report.path("modules").path(0).path("behaviors")) {
            each.put(behavior.path("name").asString(), behavior.toString());
        }
        return each;
    }

    /**
     * Each count alone and their sum leave the address read over every value: the lowercase on
     * the way to the domains stops a run only where its answer is longer than a {@code String}
     * holds, which is said of the lowercase and leaves no address open.
     */
    @Test
    void theSumIsReadAsEachCountAloneIs() {
        Map<String, String> reports = reportsOfEachGuard();
        assertEquals(new TreeSet<>(GUARDS.keySet()), reports.keySet());
        for (String guard : GUARDS.keySet()) {
            String report = reports.get(guard);
            assertFalse(report.contains("relation_shown_over_a_region"), () -> guard + report);
            assertFalse(report.contains("relation_not_shown_to_reach_every_value"),
                    () -> guard + report);
            assertTrue(report.contains("\"stopsPastTheRepresentation\"")
                    && report.contains("\"operation\":\"String.lowercase\""),
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
        Output.Examples key = new Output.Examples("demo", running.sourceIds().get(0));
        Set<String> answered = running.db().ask(key).value().rows().stream()
                .map(row -> row.resultArm().name()).collect(Collectors.toSet());
        assertEquals(Set.of("NoDuplicate", "Duplicate"), answered, examples);
    }
}
