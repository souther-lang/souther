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
        return """
                module c3

                data EmailAddress = String
                    invariant String.matches("%s", value)

                data DomainName = String
                    invariant String.matches("[a-z0-9]([a-z0-9\\\\-]*[a-z0-9])?(\\\\.[a-z0-9]([a-z0-9\\\\-]*[a-z0-9])?)+", value)
                        && String.length(value) <= 253

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
                """.formatted(emailPattern);
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
