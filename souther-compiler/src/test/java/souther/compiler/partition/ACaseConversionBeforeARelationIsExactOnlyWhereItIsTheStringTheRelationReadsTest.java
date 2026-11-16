package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.NavigableSet;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A run reaches a relation only past every case conversion before it, and a conversion ends a run
 * only for the strings whose answer is longer than a {@code String} holds. That is where the
 * representation stops, which parts no values, so a conversion before a relation stops a run for
 * no value the relation is shown over: whether it is of the string a side reads, of the strings of
 * other elements an earlier walk converts, or of a string picked out of a case of a sum through a
 * helper. What is left of the relation is what its image and the relation itself leave.
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

    private static String report(String source) {
        Compilation compilation = ACompiledModel.measured(source, Adequacy.Asked.fullReport());
        return AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }

    private static NavigableSet<String> reasons(String source) {
        String json = report(source);
        NavigableSet<String> out = new TreeSet<>();
        Matcher found = Pattern.compile("\"reason\"\\s*:\\s*\"([a-z_]+)\"").matcher(json);
        while (found.find()) {
            out.add(found.group(1));
        }
        return out;
    }

    /**
     * The walk over a list that converts the strings of every element is an application before the
     * relation, which is reached at one element. What it converts of the others stops a run only
     * where an answer is longer than a {@code String} holds, so the relation is shown over a
     * region, whether or not the walk also converts a string no side reads, and whether that string
     * is a short one or any string at all.
     */
    @Test
    void aConversionOfOtherElementsStringsByAnEarlierWalkLeavesTheRelationShownOverARegion() {
        for (String tagType : List.of("data Tag = String\n    invariant String.matches(\"[a-z]{1,2}\", value)",
                "data Tag = String")) {
            NavigableSet<String> reasons = reasons("""
                    module demo

                    %s

                    data P = { name: String, tag: Tag }
                    data Acc = { domain: String }
                    data Keyed = { domain: String, tag: String }
                    data In = { ps: List<P>, accounts: List<Acc> }

                    let keyed (ps: List<P>): List<Keyed> =
                        List.map(p -> Keyed { domain = String.lowercase(p.name),
                                              tag = String.lowercase(p.tag.value) }, ps)

                    behavior f : (i: In) -> Bool
                    let f (i) = List.any(k -> List.any(a -> String.contains(k.domain, a.domain),
                                                       i.accounts), keyed(i.ps))
                    """.formatted(tagType));
            assertTrue(reasons.contains("relation_shown_over_a_region"),
                    () -> tagType + " " + reasons);
        }
    }

    private static final String KEYED_LIST = """
            module demo

            data P = { name: String }
            data Acc = { domain: String }
            data Keyed = { domain: String }
            DECLARED

            let keyed (ps: List<P>): List<Keyed> =
                List.map(p -> Keyed { domain = String.lowercase(p.name) }, ps)

            behavior f : (i: In) -> Bool
            let f (i) = List.any(k -> List.any(a -> String.contains(k.domain, a.domain),
                                               i.accounts), keyed(i.ps))
            """;

    /**
     * The conversion of every element's string before the relation reads one element's stops a
     * run at no value the relation is shown over, whether or not the list may hold an element
     * over again: a list that keeps its elements apart is read as one that does not.
     */
    @Test
    void aListThatKeepsItsElementsApartIsReadAsOneThatDoesNot() {
        NavigableSet<String> repeating = reasons(KEYED_LIST.replace("DECLARED",
                "data In = { ps: List<P>, accounts: List<Acc> }"));
        assertTrue(repeating.contains("relation_shown_over_a_region"), repeating::toString);

        NavigableSet<String> apart = reasons(KEYED_LIST.replace("DECLARED",
                "data In = { ps: List<P>, accounts: List<Acc> }\n"
                        + "    invariant List.allDistinctBy(.name, ps)"));
        assertEquals(aboutTheRelation(repeating), aboutTheRelation(apart));
    }

    /** What is said of the relation among {@code reasons}. */
    private static List<String> aboutTheRelation(NavigableSet<String> reasons) {
        return reasons.stream().filter(each -> each.startsWith("relation_")).toList();
    }

    /**
     * What the relation is shown over is the same whether the strings are converted by a walk
     * before the relation or by the relation itself at the element it reads: the strings the
     * conversion is exact on, and so the classes the relation is drawn over, are what the single
     * conversion gives. The reports differ only in the number each position is given.
     */
    @Test
    void theConversionsOfOtherElementsLeaveTheClassesTheElementsOwnConversionGives() {
        String walked = report(KEYED_LIST.replace("DECLARED",
                "data In = { ps: List<P>, accounts: List<Acc> }"));
        String direct = report("""
                module demo

                data P = { name: String }
                data Acc = { domain: String }
                data In = { ps: List<P>, accounts: List<Acc> }

                behavior f : (i: In) -> Bool
                let f (i) = List.any(p -> List.any(a -> String.contains(String.lowercase(p.name),
                                                                         a.domain), i.accounts),
                                     i.ps)
                """);
        assertTrue(walked.contains("relation_shown_over_a_region"), walked);
        assertEquals(withoutOrdinals(direct), withoutOrdinals(walked));
    }

    /**
     * A relation of two elements of the list is not one element read: copies of one element would
     * make the two the same string, which is a row of the relation at only some values.
     */
    @Test
    void aRelationOfTwoElementsOfTheListIsNotReadAtCopiesOfOne() {
        NavigableSet<String> reasons = reasons("""
                module demo

                data P = { name: String }
                data Keyed = { domain: String }
                data In = { ps: List<P> }

                let keyed (ps: List<P>): List<Keyed> =
                    List.map(p -> Keyed { domain = String.lowercase(p.name) }, ps)

                behavior f : (i: In) -> Bool
                let f (i) = List.any(a -> List.any(b -> String.contains(a.domain, b.domain),
                                                   keyed(i.ps)), keyed(i.ps))
                """);
        assertFalse(reasons.contains("unsupported_syntax"), reasons::toString);
        assertFalse(reasons.contains("relation_shown_over_a_region"), reasons::toString);
    }

    private static String withoutOrdinals(String json) {
        return json.replaceAll("\"ordinal\"\\s*:\\s*\\d+", "\"ordinal\":0");
    }

    /**
     * A rule tying how many the list holds to how many accounts the relation reads says nothing of
     * the strings the conversion is done to, so the tie leaves the relation shown, as the list
     * without it is.
     */
    @Test
    void aListWhoseSizeIsTiedToAnotherListLeavesTheRelationShownOverARegion() {
        NavigableSet<String> reasons = reasons(KEYED_LIST.replace("DECLARED",
                "data In = { ps: List<P>, accounts: List<Acc> }\n"
                        + "    invariant List.length(ps) == List.length(accounts)"));
        assertFalse(reasons.contains("unsupported_syntax"), reasons::toString);
        assertTrue(reasons.contains("relation_shown_over_a_region"), reasons::toString);
    }

    private static final String KEYED_FROM_A_CONTAINER = """
            module demo

            data P = { name: String }
            data Acc = { domain: String }
            data Keyed = { domain: String }
            data In = { ps: CONTAINER<P>, accounts: List<Acc> }

            let keyed (ps: List<P>): List<Keyed> =
                List.map(p -> Keyed { domain = String.lowercase(p.name) }, ps)

            behavior f : (i: In) -> Bool
            let f (i) = List.any(k -> List.any(a -> String.contains(k.domain, a.domain),
                                               i.accounts), keyed(WALKED))
            """;

    /**
     * The same program over a list and over a set made into a list. The two differ in the
     * container and in nothing else, and the conversion of the other elements' strings stops a
     * run at no value the relation is shown over in either, so they are read alike.
     */
    @Test
    void aSetMadeIntoAListIsReadAsTheListIs() {
        NavigableSet<String> list = reasons(KEYED_FROM_A_CONTAINER
                .replace("CONTAINER", "List").replace("WALKED", "i.ps"));
        NavigableSet<String> set = reasons(KEYED_FROM_A_CONTAINER
                .replace("CONTAINER", "Set").replace("WALKED", "Set.toList(i.ps)"));
        assertTrue(list.contains("relation_shown_over_a_region"), list::toString);
        assertFalse(set.contains("unsupported_syntax"), set::toString);
        assertEquals(aboutTheRelation(list), aboutTheRelation(set));
    }

    /**
     * What a run reads of the pieces of a split does not turn on the separator it splits at: the
     * relation of the pieces is read whichever code point parts the string, and the code point the
     * address is written with in its pattern, and is never said not shown to reach its values or
     * not reached at them.
     */
    @Test
    void theRelationOfAPieceOfASplitIsReadWhicheverCodePointPartsTheString() {
        for (String separator : List.of("@", ",", ";", "#", "~", "/")) {
            String source = PICKED_OUT_OF_A_SUM.replace("@", separator);
            NavigableSet<String> reasons = reasons(source);
            assertFalse(reasons.contains("unsupported_syntax"), () -> separator + " " + reasons);
            assertEquals(List.of(), reasons.stream()
                    .filter(each -> each.startsWith("relation_not_shown")).toList(),
                    () -> separator + " " + reasons);
        }
    }

    /**
     * Converting both strings a side reads says of the relation what the relation of the strings
     * as they stand says: the conversions stop a run only past what a {@code String} holds.
     */
    @Test
    void theConversionsOfTheStringsASideReadsSayOfTheRelationWhatTheStringsAsTheyStandDo() {
        NavigableSet<String> converted = reasons(DECLARATIONS.replace("BODY",
                "String.contains(String.lowercase(i.a), String.lowercase(i.b))"));
        NavigableSet<String> asTheyStand = reasons(DECLARATIONS.replace("BODY",
                "String.contains(i.a, i.b)"));
        assertEquals(aboutTheRelation(asTheyStand), aboutTheRelation(converted),
                converted::toString);
        assertFalse(converted.contains("relation_not_shown_reached_at_every_value"),
                converted::toString);
    }

    /**
     * The text lowercased is picked out of whichever case of a sum a value is in, by a helper and a
     * closure handed its elements, and the relation is read once for each case the string is in.
     * The conversion stops a run only past what a {@code String} holds, so nothing of the relation
     * is left open, and it is not read as a statement about a value made from those places.
     */
    @Test
    void aTextPickedOutOfTheCasesOfASumIsTheStringAtThePlaceOfEach() {
        NavigableSet<String> reasons = reasons(PICKED_OUT_OF_A_SUM);
        assertFalse(reasons.contains("unsupported_syntax"), reasons::toString);
        assertFalse(reasons.contains("rule_about_a_derived_value"), reasons::toString);
        assertEquals(List.of(), aboutTheRelation(reasons), reasons::toString);
    }
}
