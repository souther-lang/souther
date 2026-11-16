package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.StopPastTheRepresentation;

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

    /**
     * The bounds are small: what is read does not turn on how many code points an address holds,
     * and a machine with a state for each of some hundreds is what a test pays for and says
     * nothing more by.
     */
    private static String screen(String emailPattern) {
        return screen(emailPattern, "12", "11");
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
     * round it: a bound on the domain that is the longest the address allows less the stretch it
     * needs ({@code x@}), and one more than that, are read the same.
     */
    @Test
    void aBoundOnTheDomainBesideABoundOnTheAddressIsReadWhateverTheNumbers() {
        for (String[] bounds : new String[][] {{"12", "11"}, {"12", "10"}}) {
            assertEquals(Map.of(), WhereAStringRelationIsLeftOpen.leftOpen(
                    bounded(bounds[0], bounds[1]), "screen"), List.of(bounds).toString());
        }
    }

    /**
     * An address with no bound on its length is read as well: one so long that its answer is
     * longer than a {@code String} holds ends the run at the lowercase, which is where the
     * representation stops and is said of the lowercase, and no value is open for it. The
     * flatMaps, which may make more elements than a list holds, are said beside it.
     */
    @Test
    void anAddressWithNoBoundIsReadAndTheLowercaseIsSaidToStop() {
        String source = screen("[^@\\\\s]+@[^@\\\\s]+\\\\.[^@\\\\s]+", null, "11");

        assertEquals(Map.of(), WhereAStringRelationIsLeftOpen.leftOpen(source, "screen"));
        assertEquals(List.of("List.flatMap", "String.lowercase"), WhereAStringRelationIsLeftOpen
                .evidenceOf(source, "screen").stopsPastTheRepresentation().stream()
                .map(StopPastTheRepresentation::operation).distinct().toList());
    }

    /** Whichever side of the {@code @} holds any code point, the address is read: the other three
     *  of the four languages that two sides, each any code point or letters only, make. The first,
     *  any code point on both, is read above. */
    @Test
    void anAddressIsReadWhereverItHoldsCodePointsAConversionDoesNotMapOneToOne() {
        for (String pattern : List.of(
                "[a-zA-Z0-9]+@[a-zA-Z0-9\\\\-]+\\\\.[a-zA-Z0-9.\\\\-]+",
                "[^@\\\\s]+@[a-zA-Z0-9\\\\-]+\\\\.[a-zA-Z0-9.\\\\-]+",
                "[a-z]+@[^@\\\\s]+\\\\.[^@\\\\s]+")) {
            assertEquals(Map.of(), WhereAStringRelationIsLeftOpen.leftOpen(screen(pattern),
                    "screen"), pattern);
        }
    }
}
