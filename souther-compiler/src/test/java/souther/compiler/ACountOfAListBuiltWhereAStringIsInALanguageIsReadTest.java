package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A comparison over how many a list built by a choice holds is read where what chooses is a string
 * held to a pattern, as it is where what chooses is a comparison of numbers.
 *
 * <p>What the pattern says of the string is said once, by the operation that owns it, and the
 * choice, the count and the comparison keep it: no operation is given a law of its own for the
 * count. A condition nothing says anything of is still unread, and the comparison is still
 * reported.
 *
 * <p>Each behavior below is one claim, and they share one module so that it is compiled once: the
 * arm that is counted is either, an operation with no pattern is read the same way, a step between
 * the choice and the count changes nothing, an attempt at a newtype held to a pattern is the
 * choice, and the piece the library picks at an index of the pieces of a string is the window of
 * the one piece there.
 */
class ACountOfAListBuiltWhereAStringIsInALanguageIsReadTest {

    private static final String DECLARATIONS = """
            module probe

            data Address = String
                invariant String.matches("[^@\\\\s]+@[^@\\\\s]+\\\\.[^@\\\\s]+", value)

            data Domain = String
                invariant String.matches("[a-z0-9]+(\\\\.[a-z0-9]+)+", value)
            """;

    private static final String MATCHES =
            "String.matches(\"[a-z0-9]+(\\\\.[a-z0-9]+)+\", address.value)";

    /** The piece at the index one of {@code of}, counted where it is held to the pattern. */
    private static String pickedUnder(String of) {
        return "match List.get(1, String.split(\"@\", " + of + ".value)) with | Some d -> if "
                + "String.matches(\"[a-z0-9]+(\\\\.[a-z0-9]+)+\", d) then [ d ] else [] | None -> []";
    }

    /**
     * Two strings parted by one written closure, which a behavior called twice runs over each: the
     * pieces of one are not the pieces of the other, whatever the two statements about a piece are
     * named.
     */
    private static final String TWO_STRINGS = """

            behavior heldBy : (address: Address) -> Int
            let heldBy (address) = List.length(%s)

            behavior twoStrings : (address: Address, other: Address) -> Int
            let twoStrings (address, other) = {
                guard heldBy(address) + heldBy(other) >= 1 else 0
                1
            }
            """.formatted(pickedUnder("address"));

    private static String behavior(String name, String built) {
        return """

                behavior %s : (address: Address) -> Int
                %s
                let %s (address) = {
                    let ds = %s
                    guard List.length(ds) >= 1 else 0
                    1
                }
                """.formatted(name, built.contains("Domain(") ? "    constructs Domain" : "",
                name, built);
    }

    @Test
    void whatChoosesTheCountedArmIsReadWhicheverArmItIs() {
        String source = DECLARATIONS
                + behavior("thenArm", "if " + MATCHES + " then [ address ] else []")
                + behavior("elseArm", "if " + MATCHES + " then [] else [ address ]")
                + behavior("noPattern",
                        "if String.startsWith(\"a\", address.value) then [ address ] else []")
                + behavior("stepBetween", "List.flatMap(e -> [ e ], if " + MATCHES
                        + " then [ address ] else [])")
                + behavior("attempt", "if Domain(address.value) as name then [ name ] else []")
                + behavior("pickedPiece", "match List.get(1, String.split(\"@\", address.value))"
                        + " with | Some d -> if Domain(d) as name then [ name ] else []"
                        + " | None -> []")
                + behavior("pickedMatch", pickedUnder("address"))
                + TWO_STRINGS;

        assertEquals(List.of(), notRead(report(source)));
    }

    @Test
    void aConditionNothingSaysAnythingOfStaysUnread() {
        String source = DECLARATIONS + behavior("unsaid", "if String.matches(\"[a-z]+\","
                + " String.lowercase(address.value)) then [ address ] else []");

        assertFalse(notRead(report(source)).isEmpty(), "a string made of another stands at no"
                + " position, so nothing says which strings it is");
    }

    private static String report(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static List<String> notRead(String report) {
        return report.lines().filter(line -> NotRead.isOne(line)
                || line.contains("not accounted for")).toList();
    }
}
