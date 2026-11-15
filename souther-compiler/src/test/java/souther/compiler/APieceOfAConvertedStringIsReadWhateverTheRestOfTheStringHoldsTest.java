package souther.compiler;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A piece of a lowercased string is read by what the piece itself holds. The string is cut at a
 * code point the conversion does not reach across, so the conversion of a piece is the piece's
 * own, and a code point elsewhere in the string that the conversion answers in a way no domain name
 * can be written in — {@code İ} answers an {@code i} and a combining dot — leaves nothing open.
 */
class APieceOfAConvertedStringIsReadWhateverTheRestOfTheStringHoldsTest {

    private static String screen(String emailPattern) {
        return screen(emailPattern, null, "253");
    }

    private static String screen(String emailPattern, String emailBound, String domainBound) {
        return """
                module c3

                data EmailAddress = String
                    invariant String.matches("%s", value)%s

                data DomainName = String
                    invariant String.matches("[a-z0-9]([a-z0-9\\\\-]*[a-z0-9])?(\\\\.[a-z0-9]([a-z0-9\\\\-]*[a-z0-9])?)+", value)
                        && String.length(value) <= %s

                data Account = { domain: DomainName? }

                let domainOf (email: EmailAddress): List<DomainName> =
                    List.flatMap(d -> if DomainName(d) as name then [ name ] else [],
                                 List.drop(1, String.split("@", String.lowercase(email.value))))

                let accountHasDomain (domain: DomainName, a: Account): Bool =
                    match a.domain with
                        | Some own -> own == domain
                        | None      -> false

                behavior screen : (email: EmailAddress, accounts: List<Account>) -> Int
                    constructs DomainName

                let screen (email, accounts) =
                    List.length(List.flatMap(d -> List.filter(a -> accountHasDomain(d, a), accounts),
                                             domainOf(email)))
                """.formatted(emailPattern, emailBound == null ? ""
                : " && String.length(value) <= " + emailBound, domainBound);
    }

    private static String bounded(String emailBound, String domainBound) {
        return screen("[^@\\\\s]+@[^@\\\\s]+\\\\.[^@\\\\s]+", emailBound, domainBound);
    }

    /**
     * A domain is the piece of an address whatever its length, as far as an address is written
     * round it: a domain at the longest the address allows less the stretch it needs, and one more
     * than the bound of the domain's own, are read the same, and nothing is tuned to the compiler.
     */
    @Test
    void aBoundOnTheDomainBesideABoundOnTheAddressIsReadWhateverTheNumbers() {
        for (String[] bounds : new String[][] {{"254", "253"}, {"254", "252"}}) {
            assertEquals(Map.of(), WhereAStringRelationIsLeftOpen.leftOpen(
                    bounded(bounds[0], bounds[1]), "screen"), List.of(bounds).toString());
        }
    }

    /** The four address languages of the issue: whichever side of the {@code @} holds any code
     *  point, the address is read. */
    @Test
    void anAddressIsReadWhereverItHoldsCodePointsAConversionDoesNotMapOneToOne() {
        for (String pattern : List.of(
                "[^@\\\\s]+@[^@\\\\s]+\\\\.[^@\\\\s]+",
                "[a-zA-Z0-9]+@[a-zA-Z0-9\\\\-]+\\\\.[a-zA-Z0-9.\\\\-]+",
                "[^@\\\\s]+@[a-zA-Z0-9\\\\-]+\\\\.[a-zA-Z0-9.\\\\-]+",
                "[a-z]+@[^@\\\\s]+\\\\.[^@\\\\s]+")) {
            assertEquals(Map.of(), WhereAStringRelationIsLeftOpen.leftOpen(screen(pattern),
                    "screen"), pattern);
        }
    }
}
