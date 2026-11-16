package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.BlockReason;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Where a {@code String} stops is no distinction a model made, so a relation between strings
 * leaves no string open for being long: a string is on the side the languages put it at every
 * length, however much stands round it in the other value.
 */
class AStringRelationLeavesNoStringOpenForBeingLongTest {

    private static final String EMAIL = """
            data EmailAddress = String
                invariant String.matches("[^@\\\\s]+@[^@\\\\s]+\\\\.[^@\\\\s]+", value)
            """;

    private static final String DOMAIN = """
            data DomainName = String
                invariant String.matches("[a-z0-9]([a-z0-9\\\\-]*[a-z0-9])?(\\\\.[a-z0-9]([a-z0-9\\\\-]*[a-z0-9])?)+", value)
            """;

    private static final String SCREEN = """
            data Account = { domain: DomainName? }

            let domainOf (email: EmailAddress): List<DomainName> =
                List.flatMap(d -> if DomainName(d) as name then [ name ] else [],
                             List.drop(1, String.split("@", email.value)))

            let accountHasDomain (domain: DomainName, a: Account): Bool =
                match a.domain with
                    | Some own -> own == domain
                    | None      -> false

            behavior screen : (email: EmailAddress, accounts: List<Account>) -> Int
                constructs DomainName

            let screen (email, accounts) =
                List.length(List.flatMap(d -> List.filter(a -> accountHasDomain(d, a), accounts),
                                         domainOf(email)))
            """;

    /** A domain is the domain of some address however long it is: nothing of the domains is left
     *  open. */
    @Test
    void aDomainOfAnyLengthIsOnASide() {
        assertEquals(Map.of(), WhereAStringRelationIsLeftOpen.leftOpen(
                "module c2\n" + EMAIL + DOMAIN + SCREEN, "screen"));
    }

    /** A string looked for in values of {@code [a-z]+} is shown at every length. */
    @Test
    void aStringLookedForInValuesOfNoBoundedLengthIsShownAtEveryLength() {
        assertEquals(Map.of(), WhereAStringRelationIsLeftOpen.leftOpen("""
                module d3

                data T = String
                    invariant String.matches("[a-z]+", value)

                behavior f : (p: T, bc: T) -> Bool
                let f (p, bc) = String.contains(p.value, bc.value)
                """, "f"));
    }

    /** A string looked for that is not itself a value is shown by the strings inside the values,
     *  which the language of the values bounds: nothing is open past them. */
    @Test
    void aStringLookedForInBoundedValuesIsShownByTheStringsInsideThem() {
        Map<String, List<BlockReason.RelationShownOverARegion>> open =
                WhereAStringRelationIsLeftOpen.leftOpen("""
                        module d4

                        data T = String
                            invariant String.matches("a[a-z]{2}b", value)

                        behavior f : (p: T, bc: String) -> Bool
                        let f (p, bc) = String.contains(p.value, bc)
                        """, "f");

        // A string standing in "a??b" is one of up to four code points, so none longer is
        // inside a value, and is on the false side.
        assertEquals(Map.of(), open);
    }
}
