package souther.compiler.partition;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A guard that some element of one list or some element of another exists, one by a string being
 * among the pieces of the lead's address and the other by an address being the lead's.
 *
 * <p>Each line decides where the other list has no such element, so a row is asked whether it has
 * one: whether a position's string is in the language its type admits, and whether a string
 * converted by case is among the pieces of another. A row that cannot be asked either is a row
 * the line is not drawn at, and the rule was said to be several lines this compiler does not
 * divide the input by.
 */
class AGuardOverTwoListsEachMatchedByAStringsPiecesIsDividedTest {

    private static final String MODEL = """
            module demo

            data Found
            data NoDuplicate

            data Domain = String
                invariant String.matches("[a-z0-9]+(\\\\.[a-z0-9]+)+", value)

            data EmailAddress = String
                invariant String.matches("[^@\\\\s]+@[^@\\\\s]+\\\\.[^@\\\\s]+", value)

            data PhoneNumber = String
                invariant String.matches("\\\\+?[0-9][0-9 \\\\-()]{6,19}", value)

            data EmailOnly     = { email: EmailAddress }
            data PhoneOnly     = { phone: PhoneNumber }
            data EmailAndPhone = { email: EmailAddress, phone: PhoneNumber }
            data ContactPoint  = EmailOnly | PhoneOnly | EmailAndPhone

            data Account = { domain: Domain? }

            data Contact = { reach: ContactPoint }

            let emailOf (reach: ContactPoint): List<EmailAddress> =
                match reach with
                    | EmailOnly { email }     -> [ email ]
                    | EmailAndPhone { email } -> [ email ]
                    | PhoneOnly               -> []

            let domainOf (email: EmailAddress): List<Domain> =
                List.flatMap(d -> if Domain(d) as name then [ name ] else [],
                             List.drop(1, String.split("@", String.lowercase(email.value))))

            let domainsOf (reach: ContactPoint): List<Domain> =
                List.flatMap(e -> domainOf(e), emailOf(reach))

            let reachHasEmail (email: EmailAddress, reach: ContactPoint): Bool =
                match reach with
                    | EmailOnly { email = own }     -> own == email
                    | EmailAndPhone { email = own } -> own == email
                    | PhoneOnly                     -> false

            let emailMatches (reach: ContactPoint, contacts: List<Contact>): List<Contact> =
                List.flatMap(e -> List.filter(c -> reachHasEmail(e, c.reach), contacts),
                             emailOf(reach))

            let hasDomain (domain: Domain, a: Account): Bool =
                match a.domain with
                    | Some own -> own == domain
                    | None -> false

            let onDomain (domain: Domain, accounts: List<Account>): List<Account> =
                List.filter(a -> hasDomain(domain, a), accounts)

            let accountsMatching (reach: ContactPoint, accounts: List<Account>): List<Account> =
                List.flatMap(d -> onDomain(d, accounts), domainsOf(reach))

            behavior f : (reach: ContactPoint, accounts: List<Account>, contacts: List<Contact>)
                    -> Found | NoDuplicate
                constructs Domain

            let f (reach, accounts, contacts) = {
                let matchedAccounts = List.map(a -> a.domain, accountsMatching(reach, accounts))
                let matchedContacts = List.map(c -> c.reach, emailMatches(reach, contacts))
                guard List.length(matchedAccounts) + List.length(matchedContacts) >= 1
                    else NoDuplicate
                Found
            }
            """;

    @Test
    void noLineIsLeftUndividedForWantOfAskingARowWhetherAStringIsAPiece() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, PartitionEvidence> coverage =
                compilation.db().ask(new Adequacy.Coverage("demo")).value();
        assertNotNull(coverage, "the model compiles");
        PartitionEvidence measured = coverage.get("f");
        assertNotNull(measured, "f was measured");

        assertEquals(List.of(), measured.notRead().stream()
                .filter(each -> each.reason()
                        == UndividedPosition.Reason.SEVERAL_LINES_IN_ONE_RULE)
                .toList());
    }
}
