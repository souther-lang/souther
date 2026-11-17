package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A count over what a lookup built from the domain part of an address and from the address
 * itself is read, wherever the way to the count states something of the pieces of the address.
 *
 * <p>Three relations meet at the count: the domain of an account against the piece of the
 * lowercased address, which the way holds to a language and to some account having it, the
 * address of a contact against the address of the lead, and a line on how many separators the
 * address holds. Each is a statement of the same positions, read in the cases where the count
 * turns on it, and none of them is stated of strings the others leave out. What the way says of
 * a piece of the address leaves the strings of the address as the language of the piece parts
 * them, and a case where no address has the separator is no case a row is in, since every
 * address the declarations allow holds one.
 */
class AStringBesideAPieceOfItIsReadWhereTheWayStatesTheTwoTest {

    private static final String SOURCE = """
            module probe

            data Email = String
                invariant String.matches("[^@\\\\s]+@[^@\\\\s]+\\\\.[^@\\\\s]+", value)

            data Domain = String
                invariant String.matches("[a-z0-9]([a-z0-9\\\\-]*[a-z0-9])?(\\\\.[a-z0-9]([a-z0-9\\\\-]*[a-z0-9])?)+", value)

            data Account = { domain: Domain? }

            data Contact = { email: Email }

            let domainOf (email: Email): List<Domain> =
                match List.get(1, String.split("@", String.lowercase(email.value))) with
                    | Some d -> if Domain(d) as name then [ name ] else []
                    | None   -> []

            let hasDomain (domain: Domain, a: Account): Bool =
                match a.domain with
                    | Some own -> own == domain
                    | None     -> false

            let matches (email: Email, accounts: List<Account>): List<Account> =
                List.flatMap(d -> List.filter(a -> hasDomain(d, a), accounts), domainOf(email))

            let sameEmail (email: Email, c: Contact): Bool = c.email == email

            behavior screen : (email: Email, accounts: List<Account>, contacts: List<Contact>) -> Int
                constructs Domain
            let screen (email, accounts, contacts) = {
                let found = matches(email, accounts)
                let people = List.filter(c -> sameEmail(email, c), contacts)
                guard List.length(found) + List.length(people) >= 1 else 0
                1
            }
            """;

    /**
     * The same count over lookups made of a sum: the address of a lead or contact is a case of
     * what it can be reached by, and the ids of what matched are made distinct. Rows reach the
     * comparison of two addresses along ways that part them by different strings, and along one
     * that parts them by none.
     */
    private static final String OF_A_SUM = """
            module probe

            data Email = String
                invariant String.matches("[^@\\\\s]+@[^@\\\\s]+\\\\.[^@\\\\s]+", value)

            data Phone = String
                invariant String.length(value) >= 3

            data Domain = String
                invariant String.matches("[a-z0-9]([a-z0-9\\\\-]*[a-z0-9])?(\\\\.[a-z0-9]([a-z0-9\\\\-]*[a-z0-9])?)+", value)

            data AccountId = String
                invariant String.length(value) >= 1

            data ContactId = String
                invariant String.length(value) >= 1

            data EmailOnly = { email: Email }
            data EmailAndPhone = { email: Email, phone: Phone }
            data ContactPoint = EmailOnly | EmailAndPhone

            data Account = { id: AccountId, domain: Domain? }

            data Contact = { id: ContactId, reach: ContactPoint }

            let emailOf (reach: ContactPoint): List<Email> =
                match reach with
                    | EmailOnly { email }     -> [ email ]
                    | EmailAndPhone { email } -> [ email ]

            let domainOf (email: Email): List<Domain> =
                match List.get(1, String.split("@", String.lowercase(email.value))) with
                    | Some d -> if Domain(d) as name then [ name ] else []
                    | None   -> []

            let accountHasDomain (domain: Domain, a: Account): Bool =
                match a.domain with
                    | Some own -> own == domain
                    | None     -> false

            let domainMatches (reach: ContactPoint, accounts: List<Account>): List<Account> =
                List.flatMap(e -> List.flatMap(d -> List.filter(a -> accountHasDomain(d, a),
                    accounts), domainOf(e)), emailOf(reach))

            let reachHasEmail (email: Email, reach: ContactPoint): Bool =
                match reach with
                    | EmailOnly { email = own }     -> own == email
                    | EmailAndPhone { email = own } -> own == email

            let emailMatches (reach: ContactPoint, contacts: List<Contact>): List<Contact> =
                List.flatMap(e -> List.filter(c -> reachHasEmail(e, c.reach), contacts),
                    emailOf(reach))

            behavior screen : (reach: ContactPoint, accounts: List<Account>,
                    contacts: List<Contact>) -> Int
                constructs Domain
            let screen (reach, accounts, contacts) = {
                let matchedAccounts = domainMatches(reach, accounts)
                let matchedContacts = emailMatches(reach, contacts)
                guard List.length(matchedAccounts) + List.length(matchedContacts) >= 1 else 0
                1
            }
            """;

    private static List<String> unreadIn(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        String page = AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
        return page.lines().filter(line -> line.contains("not read")
                || line.contains("not accounted for")).toList();
    }

    @Test
    void everyPlaceTheCountNamesIsReadWhereTheWayStatesThePiece() {
        assertEquals(List.of(), unreadIn(SOURCE));
    }

    @Test
    void everyPlaceTheCountNamesIsReadWhereTheLookupsAreMadeOfASum() {
        assertEquals(List.of(), unreadIn(OF_A_SUM));
    }
}
