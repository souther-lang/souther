package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A run reaches a relation only past every case conversion before it, and a conversion ends a run
 * for the strings it is not a map of code points on. A conversion of a string no side of the
 * relation reads ends a run at values of that string alone, so it takes no value of the sides
 * away where the string is chosen apart from them and some string it holds is one the conversion
 * ends no run for.
 *
 * <p>Here the address a first list converts is not what the second list's relation reads, and the
 * second list's domains are still reached at every value. Where the address is tied by a rule to
 * the string the relation reads, or holds no string the conversion is a map on, they are not.
 */
class AConversionOfAStringNoSideReadsLeavesTheRelationReachedTest {

    private static final String DECLARATIONS = """
            module demo

            data Domain = String
                invariant String.matches("[a-z0-9.]+", value)
            ADDRESS

            data Acc = { name: String, domain: Domain? }
            data Lead = { addr: Address, other: String }LEADRULE
            data In = { lead: Lead, accounts: List<Acc> }

            let domainsOf (a: Address): List<Domain> =
                List.flatMap(d -> if Domain(d) as name then [ name ] else [],
                             String.split("@", String.lowercase(a.value)))

            let upperOf (a: Address): List<Domain> =
                List.flatMap(d -> if Domain(d) as name then [ name ] else [],
                             String.split("@", String.uppercase(a.value)))

            let othersOf (s: String): List<Domain> =
                List.flatMap(d -> if Domain(d) as name then [ name ] else [],
                             String.split("@", String.lowercase(s)))

            let accountHas (d: Domain, a: Acc): Bool =
                match a.domain with
                    | Some own -> own == d
                    | None     -> false

            let onDomain (d: Domain, accounts: List<Acc>): List<Acc> =
                List.filter(a -> accountHas(d, a), accounts)

            data Hit = { n: Int }
            data Miss = { n: Int }

            behavior f : (i: In) -> Hit | Miss
                constructs Hit, Miss, Domain
            let f (i) = {
                let xs = List.flatMap(d -> onDomain(d, i.accounts), domainsOf(i.lead.addr))
                BEFORE
                let ys = List.flatMap(d -> onDomain(d, i.accounts), othersOf(i.lead.other))
                guard List.length(ys) >= 1 else Miss { n = 0 }
                Hit { n = List.length(xs) }
            }
            """;

    private static String reasons(String address, String leadRule) {
        return reasons(address, leadRule, "");
    }

    /** {@code before} is written between the first list and the second, so a run reaches the
     *  second list's relation past it. */
    private static String reasons(String address, String leadRule, String before) {
        Compilation compilation = Compilation.ofSource(DECLARATIONS.replace("ADDRESS", address)
                .replace("LEADRULE", leadRule).replace("BEFORE", before), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        return AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }

    @Test
    void anAddressConvertedBeforeIsNoStopOfTheRelationReadElsewhere() {
        String report = reasons("data Address = String", "");
        assertTrue(report.contains("relation_shown_over_a_region"), report);
        assertFalse(report.contains("relation_not_shown_to_reach_every_value"), report);
    }

    @Test
    void anAddressHoldingNoStringTheConversionIsAMapOnIsOne() {
        String report = reasons("""
                data Address = String
                    invariant String.matches("[İ]+", value)""", "");
        assertTrue(report.contains("relation_not_shown_to_reach_every_value"), report);
    }

    private static final String AND_UPPERCASED =
            "let zs = List.flatMap(d -> onDomain(d, i.accounts), upperOf(i.lead.addr))";

    /**
     * Each conversion of one string has strings it is a map on, and a run gets past both only at
     * strings that are among the strings of each: {@code ß} is a map of one code point under
     * lowercase and becomes two under uppercase, {@code İ} the other way about.
     */
    @Test
    void twoConversionsOfOneStringAreGotPastAtTheStringsBothAreAMapOn() {
        String apart = reasons("""
                data Address = String
                    invariant String.matches("[ßİ]+", value)""", "", AND_UPPERCASED);
        assertTrue(apart.contains("relation_not_shown_to_reach_every_value"), apart);

        String alike = reasons("""
                data Address = String
                    invariant String.matches("[a-z]+", value)""", "", AND_UPPERCASED);
        assertTrue(alike.contains("relation_shown_over_a_region"), alike);
        assertFalse(alike.contains("relation_not_shown_to_reach_every_value"), alike);
    }

    @Test
    void anAddressTiedByARuleToWhatTheRelationReadsIsOne() {
        String report = reasons("data Address = String", """

                    invariant sameLength = String.length(addr.value) == String.length(other)""");
        assertTrue(report.contains("relation_not_shown_to_reach_every_value"), report);
    }
}
