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

    /** What a customer model writes: a construction attempted on each piece, kept where it holds. */
    @Test
    void aWalkOverWhatAFlatMapAnswersOverThePiecesIsProvedToo() {
        Compilation compilation = measured("""
                module repro.flat

                data Address = String
                    invariant String.matches("[^@\\\\s]+@[^@\\\\s]+\\\\.[^@\\\\s]+", value)

                data Domain = String
                    invariant String.matches("[a-z0-9.]+", value)

                let domainOf (a: Address): List<Domain> =
                    List.flatMap(d -> if Domain(d) as name then [ name ] else [],
                                 List.drop(1, String.split("@", String.lowercase(a.value))))

                behavior lengths : (a: Address) -> List<Int>
                let lengths (a) = List.map(s -> String.length(s.value), domainOf(a))

                example lengths
                    | "two" : (Address("a@b.c")) -> [ 3 ]
                """);
        assertEquals(List.of(), walkRewritesOwedOf("flatMap", compilation));
        assertEquals(List.of(), walkRewritesOwedOf("map", compilation));
    }

    /**
     * The address comes from the arms of a {@code match}, each binding it apart, and one walk reads
     * it through all of them. What is known of the one value the arms stand for is the same whichever
     * arm reached it, so measuring it is not refused for saying two things of it.
     */
    @Test
    void anAddressBoundApartByEachArmOfAMatchIsOneValueToWhatIsKnownOfIt() {
        Compilation compilation = measured("""
                module repro.arms

                data Address = String
                    invariant String.matches("[^@\\\\s]+@[^@\\\\s]+\\\\.[^@\\\\s]+", value)

                data Phone = String
                    invariant String.length(value) >= 1

                data DomainName = String
                    invariant String.matches("[a-z0-9.]+", value)

                data EmailOnly     = { email: Address }
                data PhoneOnly     = { phone: Phone }
                data EmailAndPhone = { email: Address, phone: Phone }
                data ContactPoint  = EmailOnly | PhoneOnly | EmailAndPhone

                let emailOf (reach: ContactPoint): List<Address> =
                    match reach with
                        | EmailOnly { email }     -> [ email ]
                        | EmailAndPhone { email } -> [ email ]
                        | PhoneOnly               -> []

                let domainOf (a: Address): List<DomainName> =
                    List.flatMap(d -> if DomainName(d) as name then [ name ] else [],
                                 List.drop(1, String.split("@", String.lowercase(a.value))))

                let domainsOf (reach: ContactPoint): List<DomainName> =
                    List.flatMap(e -> domainOf(e), emailOf(reach))

                behavior sizes : (reach: ContactPoint) -> List<Int>
                let sizes (reach) = List.map(d -> String.length(d.value), domainsOf(reach))

                example sizes
                    | "both" : (EmailAndPhone { email = Address("a@b.c"), phone = Phone("1") }) -> [ 3 ]
                """);
        assertEquals(List.of(), walkRewritesOwedOf("flatMap", compilation).stream()
                .filter(rewrite -> !List.of("fold_after_one_step", "fold_from_the_seed")
                        .contains(rewrite)).toList());
    }

    /** A list a {@code match} builds holds the most its arms hold, so a flatMap over it that adds one
     *  for each holds one at most. */
    @Test
    void aFlatMapOverTheListOfAMatchWhoseArmsHoldOneAtMostIsAWalkOverOneAtMost() {
        assertEquals(List.of(), walkRewritesOwed(measured("""
                module repro.source
                data Seen = { n: Int }
                data Held = Nobody | Seen

                let heldOf (h: Held): List<Int> =
                    match h with
                        | Nobody     -> []
                        | Seen { n } -> [ n ]

                behavior sizes : (h: Held) -> List<Int>
                let sizes (h) = List.map(m -> m + 1, List.flatMap(e -> [ e ], heldOf(h)))

                example sizes
                    | "none" : (Nobody) -> [ ]
                """)));
    }

    /** What a closure answers is bounded by what the type of its parameter guarantees, whatever it
     *  is handed. */
    @Test
    void aFlatMapWhoseClosureAnswersOneAtMostForEveryAddressIsAWalkOverOneAtMost() {
        assertEquals(List.of(), walkRewritesOwed(measured("""
                module repro.closure
                data Address = String
                    invariant String.matches("[^@\\\\s]+@[^@\\\\s]+", value)

                behavior lengths : (a: Address) -> List<Int>
                let lengths (a) =
                    List.map(s -> String.length(s),
                             List.flatMap(e -> List.drop(1, String.split("@", e.value)), [ a ]))

                example lengths
                    | "one" : (Address("a@bc")) -> [ 2 ]
                """)));
    }

    /** A walk inside a closure goes over a list built from the closure's parameter, so the list
     *  is one value there as it is anywhere. */
    @Test
    void aWalkInsideAClosureOverWhatItsParameterSplitsIsAWalkOverOneAtMost() {
        assertEquals(List.of(), walkRewritesOwed(measured("""
                module repro.inside
                data Address = String
                    invariant String.matches("[^@\\\\s]+@[^@\\\\s]+", value)

                behavior lengths : (a: Address) -> List<Int>
                let lengths (a) =
                    List.flatMap(e -> List.map(s -> String.length(s),
                                               List.drop(1, String.split("@", e.value))),
                                 [ a ])

                example lengths
                    | "one" : (Address("a@bc")) -> [ 2 ]
                """)));
    }

    @Test
    void aMatchOneOfWhoseArmsHoldSeveralIsNotAWalkOverOneAtMost() {
        assertEquals(List.of("fold_after_one_step", "fold_from_the_seed"),
                walkRewritesOwed(measured("""
                        module repro.several
                        data Seen = { n: Int }
                        data Held = Nobody | Seen

                        let twiceOf (h: Held): List<Int> =
                            match h with
                                | Nobody     -> []
                                | Seen { n } -> [ n, n ]

                        behavior sizes : (h: Held) -> List<Int>
                        let sizes (h) =
                            List.map(m -> m + 1, List.flatMap(e -> [ e ], twiceOf(h)))

                        example sizes
                            | "none" : (Nobody) -> [ ]
                        """)));
    }

    @Test
    void aClosureThatAnswersSeveralForSomeArgumentIsNotAWalkOverOneAtMost() {
        assertEquals(List.of("fold_after_one_step", "fold_from_the_seed"),
                walkRewritesOwed(measured("""
                        module repro.severalpieces
                        data Address = String
                            invariant String.matches("[^@\\\\s]+@[^@\\\\s]+", value)

                        behavior lengths : (a: Address) -> List<Int>
                        let lengths (a) =
                            List.map(s -> String.length(s),
                                     List.flatMap(e -> String.split("@", e.value), [ a ]))

                        example lengths
                            | "one" : (Address("a@bc")) -> [ 1, 2 ]
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

    @Test
    void theSameValueReachedAsTheLibrarysDropAndAsItsBodyWrittenOutIsMeasured() {
        measured("""
                module repro.routes

                behavior both : (xs: List<Int>) -> List<Int>
                let both (xs) = {
                    let a = List.drop(1, xs)
                    let (_, b) = List.fold(
                        (acc, x) -> {
                            let (i, ys) = acc
                            let next = i + 1
                            if i >= 1 then (next, ys ++ [x]) else (next, ys)
                        },
                        (0, []),
                        xs
                    )
                    List.map(s -> s + 1, a) ++ List.map(s -> s + 2, b)
                }

                example both
                    | "one" : ([1, 2, 3]) -> [3, 4, 4, 5]
                """);
    }

    @Test
    void theSameValueReachedFirstAsItsBodyWrittenOutAndThenAsTheLibrarysDropIsMeasured() {
        measured("""
                module repro.routes

                behavior both : (xs: List<Int>) -> List<Int>
                let both (xs) = {
                    let (_, b) = List.fold(
                        (acc, x) -> {
                            let (i, ys) = acc
                            let next = i + 1
                            if i >= 1 then (next, ys ++ [x]) else (next, ys)
                        },
                        (0, []),
                        xs
                    )
                    let a = List.drop(1, xs)
                    List.map(s -> s + 2, b) ++ List.map(s -> s + 1, a)
                }

                example both
                    | "one" : ([1, 2, 3]) -> [4, 5, 3, 4]
                """);
    }

    /** The rewrites of the walk of {@code List.map} that are owed, as the obligation list says. */
    private static List<String> walkRewritesOwed(Compilation compilation) {
        return walkRewritesOwedOf("map", compilation);
    }

    /** The same, of the walk of the library operation {@code definition} names. */
    private static List<String> walkRewritesOwedOf(String definition, Compilation compilation) {
        JsonNode replacement = JSON.readTree(AdequacyReport.of(compilation)
                        .json(SourceRendering.namedByIdentity(compilation.texts())))
                .get("modules").get(0).get("behaviors").get(0).get("replacement");
        List<String> owed = new ArrayList<>();
        for (JsonNode each : replacement.get("obligations")) {
            JsonNode id = each.get("obligationId");
            if (id.has("definition") && id.get("definition").asString().equals(definition)
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
