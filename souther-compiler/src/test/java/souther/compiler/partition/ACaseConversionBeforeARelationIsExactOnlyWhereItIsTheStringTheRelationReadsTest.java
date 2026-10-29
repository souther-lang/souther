package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A run reaches a relation only past every case conversion before it, and a conversion ends a run
 * for the strings whose answer is longer than a {@code String} holds. What a relation is shown over
 * is what a run reaches it at, so a conversion is let go of only where what it ends a run for is
 * said exactly: it is the conversion of a text that is the string at a place a side of the relation
 * reads, and the strings it is exactly a map on are the ones it ends no run for.
 *
 * <p>That a text is the string at a place is not that it is made from a string there. A name a
 * closure is handed is followed to what it stands for, through a helper that picks it out of a case
 * of a sum, to the string; and where it stands for one of several, to every one.
 */
class ACaseConversionBeforeARelationIsExactOnlyWhereItIsTheStringTheRelationReadsTest {

    private static final String DECLARATIONS = """
            module demo

            data In = { a: String, b: String }

            behavior f : (i: In) -> Bool
            let f (i) = BODY
            """;

    /** The shape the email-and-domain rules of the CRM example come to: a string is picked out of
     *  a case of a sum, lowercased inside a helper, and compared with one of a list. */
    private static final String PICKED_OUT_OF_A_SUM = """
            module demo

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

            data Account = { name: String, domain: DomainName? }

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
                    | None     -> false

            behavior f : (reach: ContactPoint, accounts: List<Account>) -> List<Account>
            let f (reach, accounts) =
                List.flatMap(d -> List.filter(a -> accountHasDomain(d, a), accounts),
                             domainsOf(reach))
            """;

    private static SortedSet<String> reasons(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String json = AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
        SortedSet<String> out = new TreeSet<>();
        Matcher found = Pattern.compile("\"reason\"\\s*:\\s*\"([a-z_]+)\"").matcher(json);
        while (found.find()) {
            out.add(found.group(1));
        }
        return out;
    }

    @Test
    void theConversionsOfTheStringsASideReadsLeaveTheRelationShownOverARegion() {
        SortedSet<String> reasons = reasons(DECLARATIONS.replace("BODY",
                "String.contains(String.lowercase(i.a), String.lowercase(i.b))"));
        assertTrue(reasons.contains("relation_shown_over_a_region"), reasons::toString);
        assertFalse(reasons.contains("relation_not_shown_to_reach_every_value"),
                reasons::toString);
        assertFalse(reasons.contains("relation_not_shown_reached_at_every_value"),
                reasons::toString);
    }

    /**
     * The text lowercased is picked out of whichever case of a sum a value is in, by a helper and a
     * closure handed its elements, and the relation is read once for each case the string is in.
     * It is the string at the place of each case, so the relation is shown over a region: were the
     * text taken for a value made from those places, the conversion would be a stop at values
     * nothing says, and the relation would be shown reached at none.
     */
    @Test
    void aTextPickedOutOfTheCasesOfASumIsTheStringAtThePlaceOfEach() {
        SortedSet<String> reasons = reasons(PICKED_OUT_OF_A_SUM);
        assertTrue(reasons.contains("relation_shown_over_a_region"), reasons::toString);
        assertFalse(reasons.contains("unsupported_syntax"), reasons::toString);
        assertEquals(List.of(), reasons.stream()
                .filter(each -> each.startsWith("relation_not_shown")).toList(),
                reasons::toString);
    }
}
