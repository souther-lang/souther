package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A walk over the pieces of a string split at a character that the invariant of the string's type
 * lets stand once is a walk over a list of one element at most, once the first piece is dropped.
 * It owes neither rewrite, as a walk over any list of one element at most does; where the invariant
 * lets the character stand more often, or the pattern is not one whose count of it can be told,
 * both are owed as before.
 */
class AWalkOverThePiecesOfASplitAtACharacterAnInvariantAllowsOnceOwesNoRewriteTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    @Test
    void aSeparatorThePatternAllowsOnceLeavesAtMostOnePieceAfterTheFirst() {
        assertEquals(List.of(), walkRewritesOwed(measured("""
                module repro.once

                data Address = String
                    invariant String.matches("[^@\\\\s]+@[^@\\\\s]+", value)

                behavior lengths : (a: Address) -> List<Int>
                let lengths (a) =
                    List.map(s -> String.length(s), List.drop(1, String.split("@", a.value)))

                example lengths
                    | "one" : (Address("a@bc")) -> [ 2 ]
                """)));
    }

    @Test
    void aCaseConversionOfTheStringBeforeTheSplitChangesNothingOfTheCount() {
        assertEquals(List.of(), walkRewritesOwed(measured("""
                module repro.lowercase

                data Address = String
                    invariant String.matches("[^@\\\\s]+@[^@\\\\s]+", value)

                behavior lengths : (a: Address) -> List<Int>
                let lengths (a) =
                    List.map(s -> String.length(s),
                             List.drop(1, String.split("@", String.lowercase(a.value))))

                example lengths
                    | "one" : (Address("A@bc")) -> [ 2 ]
                """)));
    }

    /** The pattern of an address as a customer model writes it, and a helper that is expanded
     *  at two places. */
    @Test
    void aHelperExpandedAtSeveralPlacesIsProvedAtEveryWalkItReaches() {
        assertEquals(List.of(), walkRewritesOwed(measured("""
                module repro.helper

                data Address = String
                    invariant String.matches("[^@\\\\s]+@[^@\\\\s]+\\\\.[^@\\\\s]+", value)

                let domainOf (a: Address): List<String> =
                    List.drop(1, String.split("@", String.lowercase(a.value)))

                behavior lengths : (a: Address, b: Address) -> List<Int>
                let lengths (a, b) =
                    List.append(List.map(s -> String.length(s), domainOf(a)),
                                List.map(s -> String.length(s) + 1, domainOf(b)))

                example lengths
                    | "two" : (Address("a@b.c"), Address("d@e.f")) -> [ 3, 4 ]
                """)));
    }

    @Test
    void aHelperThatAnswersThePiecesIsReadThroughItsExpansion() {
        assertEquals(List.of(), walkRewritesOwed(measured("""
                module repro.helper

                data Address = String
                    invariant String.matches("[^@\\\\s]+@[^@\\\\s]+\\\\.[^@\\\\s]+", value)

                let domainOf (a: Address): List<String> =
                    List.drop(1, String.split("@", String.lowercase(a.value)))

                behavior lengths : (a: Address) -> List<Int>
                let lengths (a) = List.map(s -> String.length(s), domainOf(a))

                example lengths
                    | "two" : (Address("a@b.c")) -> [ 3 ]
                """)));
    }

    @Test
    void aPatternThatLetsTheSeparatorStandAsOftenAsItLikesLeavesBothRewritesOwed() {
        assertEquals(List.of("fold_after_one_step", "fold_from_the_seed"),
                walkRewritesOwed(measured("""
                        module repro.several

                        data Address = String
                            invariant String.matches("[^\\\\s]+@[^\\\\s]+", value)

                        behavior lengths : (a: Address) -> List<Int>
                        let lengths (a) =
                            List.map(s -> String.length(s),
                                     List.drop(1, String.split("@", a.value)))

                        example lengths
                            | "one" : (Address("a@bc")) -> [ 2 ]
                        """)));
    }

    @Test
    void aSeparatorOfSeveralCodePointsSaysNothingOfTheCount() {
        assertEquals(List.of("fold_after_one_step", "fold_from_the_seed"),
                walkRewritesOwed(measured("""
                        module repro.longer

                        data Address = String
                            invariant String.matches("[^@\\\\s]+@[^@\\\\s]+", value)

                        behavior lengths : (a: Address) -> List<Int>
                        let lengths (a) =
                            List.map(s -> String.length(s),
                                     List.drop(1, String.split("@@", a.value)))

                        example lengths
                            | "one" : (Address("a@bc")) -> [ ]
                        """)));
    }

    /** The rewrites of the walk of {@code List.map} that are owed, as the obligation list says. */
    private static List<String> walkRewritesOwed(Compilation compilation) {
        JsonNode replacement = JSON.readTree(AdequacyReport.of(compilation)
                        .json(SourceRendering.namedByIdentity(compilation.texts())))
                .get("modules").get(0).get("behaviors").get(0).get("replacement");
        List<String> owed = new ArrayList<>();
        for (JsonNode each : replacement.get("obligations")) {
            JsonNode id = each.get("obligationId");
            if (id.has("definition") && id.get("definition").asString().equals("map")
                    && id.get("rewrite").asString().startsWith("fold_")) {
                owed.add(id.get("rewrite").asString());
            }
        }
        return owed;
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        return ACompiledModel.compiles(compilation);
    }
}
