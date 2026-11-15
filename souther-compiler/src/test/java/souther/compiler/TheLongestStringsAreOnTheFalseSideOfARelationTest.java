package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.BlockReason;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A string longer than any partner can be written round is shown on the false side of a relation,
 * and a string that needs nothing written round it is shown at every length: the longest strings
 * are left in no class only where the room round a string is not worked out.
 */
class TheLongestStringsAreOnTheFalseSideOfARelationTest {

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

    /**
     * An address is at least two code points longer than its domain, so a domain longer than the
     * longest string less two is the domain of no address: it is on the side no address is, and
     * nothing of the domains is left open.
     */
    @Test
    void aDomainLongerThanAnyAddressWrittenRoundItIsNoAddressesDomain() {
        assertEquals(Map.of(), WhereAStringRelationIsLeftOpen.leftOpen(
                "module c2\n" + EMAIL + DOMAIN + SCREEN, "screen"));
    }

    /**
     * A string that is a value stands in a value with nothing written round it. A string looked
     * for in values of {@code [a-z]+} is itself one, whatever its length, so it is shown at every
     * length.
     */
    @Test
    void aStringThatIsAValueNeedsNothingWrittenRoundItToStandInOne() {
        assertEquals(Map.of(), WhereAStringRelationIsLeftOpen.leftOpen("""
                module d3

                data T = String
                    invariant String.matches("[a-z]+", value)

                behavior f : (p: T, bc: T) -> Bool
                let f (p, bc) = String.contains(p.value, bc.value)
                """, "f"));
    }

    /**
     * Where a string looked for is not itself a value, what is written round it is what the
     * machine of the values needs: the open region stops at the longest string less that, and not
     * at a guess from how many states the machine has.
     */
    @Test
    void theRoomRoundAStringIsWhatTheMachineOfTheValuesNeeds() {
        Map<String, List<BlockReason.RelationShownOverARegion>> open =
                WhereAStringRelationIsLeftOpen.leftOpen("""
                        module d4

                        data T = String
                            invariant String.matches("a[a-z]{2}b", value)

                        behavior f : (p: T, bc: String) -> Bool
                        let f (p, bc) = String.contains(p.value, bc)
                        """, "f");

        // A string standing in "a??b" is one of up to four code points, so none longer is
        // a value's string; the strings of the longest string less nothing are all on the false side.
        assertEquals(Map.of(), open);
    }
}
