package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
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
                let ys = List.flatMap(d -> onDomain(d, i.accounts), othersOf(i.lead.other))
                guard List.length(ys) >= 1 else Miss { n = 0 }
                Hit { n = List.length(xs) }
            }
            """;

    private static String reasons(String address, String leadRule) {
        Compilation compilation = Compilation.ofSource(DECLARATIONS.replace("ADDRESS", address)
                .replace("LEADRULE", leadRule), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(e -> e.diagnostic().code() + " " + e.diagnostic().said()).toList());
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

    @Test
    void anAddressTiedByARuleToWhatTheRelationReadsIsOne() {
        String report = reasons("data Address = String", """

                    invariant sameLength = String.length(addr.value) == String.length(other)""");
        assertTrue(report.contains("relation_not_shown_to_reach_every_value"), report);
    }
}
