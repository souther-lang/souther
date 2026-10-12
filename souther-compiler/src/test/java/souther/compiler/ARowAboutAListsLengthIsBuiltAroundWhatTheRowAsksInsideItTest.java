package souther.compiler;

import souther.compiler.partition.GenerationOutcome;
import souther.compiler.partition.Generator;
import souther.compiler.partition.ObligationIdentity;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Offering;
import souther.compiler.query.OfferingRequest;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row standing at a class of how many a list holds and at a class of what its elements hold is a
 * list built to hold such an element, to a size the first class takes.
 *
 * <p>The class of the length says how many, and the class inside says what one of them holds, so
 * the two are one list asked two things. Written as the length class's own value — a list of some
 * size — the list would leave the element nowhere to be written, and no row standing at both would
 * ever be offered.
 *
 * <p>And a class of the length that leaves the list nothing to hold is no class to put beside one
 * inside it. A row about the empty list stands at no class of what the elements hold, rather than
 * at one no empty list can be in.
 */
class ARowAboutAListsLengthIsBuiltAroundWhatTheRowAsksInsideItTest {

    private static final String MODEL = """
            module example.quote

            import List ( filter, all, length )

            data Item = { quantity: Int, unitPrice: Int }
            data Cart = { items: List<Item> }

            data Empty
            data Bad = { count: Int }
            data Priced = { total: Int }

            behavior quote : (c: Cart) -> Priced | Empty | Bad
                constructs Priced, Bad

            let quote (c) = {
                guard length(c.items) >= %d else Empty
                guard all(i -> i.quantity >= 1, c.items) else Bad { count = length(filter(i -> i.quantity < 1, c.items)) }
                Priced { total = 0 }
            }

            example quote
            """;

    /**
     * Only an empty list written, and every class of what an element holds offered a row — with an
     * element in it, standing in the class.
     */
    @Test
    void aClassInsideTheListIsOfferedARowBesideOnlyAnEmptyOne() {
        List<Adequacy.GenerationDisposition> said = generated(1, """
                    | "empty" : (Cart { items = [] }) -> Empty
                """);

        for (String cls : List.of("c.items[*].quantity/x < 1", "c.items[*].quantity/1 <= x",
                "List.length(c.items)/0 < x")) {
            List<String> rows = rowsFor(said, Set.of(cls));
            assertTrue(!rows.isEmpty() && rows.stream().allMatch(row -> row.contains("Item {")),
                    () -> "a row with an element is offered for " + cls + ": " + said);
        }
    }

    /** Only lists with an element written, and the empty list offered as itself. */
    @Test
    void anEmptyListIsOfferedARowBesideOnlyOnesWithElements() {
        List<Adequacy.GenerationDisposition> said = generated(1, """
                    | "ok" : (Cart { items = [Item { quantity = 1, unitPrice = 1 }] }) -> Priced { total = 0 }
                """);

        assertEquals(List.of("Cart { items = [] }"),
                rowsFor(said, Set.of("List.length(c.items)/0 <= x <= 0")),
                () -> "the empty list stands at no class of what it would hold: " + said);
    }

    /**
     * A length class that starts above one, beside a class inside: the list holds as many as the
     * length class asks.
     */
    @Test
    void theListHoldsAsManyAsTheLengthClassAsks() {
        List<Adequacy.GenerationDisposition> said = generated(2, """
                    | "empty" : (Cart { items = [] }) -> Empty
                """);

        List<String> rows = rowsFor(said,
                Set.of("List.length(c.items)/2 <= x", "c.items[*].quantity/x < 1"));
        assertTrue(!rows.isEmpty() && rows.stream().allMatch(row -> elementsIn(row) >= 2),
                () -> "two elements at least, for the pair of the two classes: " + said);
    }

    /**
     * A length class that admits none and some: the row asking for an element as well holds one,
     * which is a count the class takes, and not the none its values may have been written at.
     */
    @Test
    void aLengthClassTakingNoneAndSomeHoldsTheElementAsked() {
        List<Adequacy.GenerationDisposition> said = generated(2, """
                    | "empty" : (Cart { items = [] }) -> Empty
                """);

        for (String inside : List.of("c.items[*].quantity/x < 1", "c.items[*].quantity/1 <= x")) {
            List<String> rows = rowsFor(said, Set.of("List.length(c.items)/0 <= x < 2", inside));
            assertTrue(!rows.isEmpty() && rows.stream().allMatch(row -> elementsIn(row) == 1),
                    () -> "one element, for " + inside + " beside a list of fewer than two: "
                            + said);
        }
    }

    private static int elementsIn(String row) {
        return row.split("Item \\{", -1).length - 1;
    }

    /** The first input of every row offered for the obligation naming exactly {@code classes}. */
    private static List<String> rowsFor(List<Adequacy.GenerationDisposition> said,
                                        Set<String> classes) {
        for (Adequacy.GenerationDisposition each : said) {
            if (each.item().isPresent() && classIdsOf(each.item().get()).equals(classes)) {
                if (!(each.outcome() instanceof GenerationOutcome.Generated generated)) {
                    return List.of();
                }
                List<String> out = new ArrayList<>();
                for (Generator.GeneratedRow row : generated.candidates()) {
                    out.add(row.inputs().getFirst().text());
                }
                return out;
            }
        }
        throw new AssertionError("nothing is owed at " + classes + ": " + said);
    }

    private static Set<String> classIdsOf(ObligationIdentity item) {
        return switch (item) {
            case ObligationIdentity.OfAClass one -> Set.of(one.classOfAPosition().classId());
            case ObligationIdentity.OfAFallbackPairCell pair -> {
                Set<String> ids = new LinkedHashSet<>();
                pair.classes().forEach(each -> ids.add(each.classId()));
                yield ids;
            }
            default -> Set.of();
        };
    }

    private static List<Adequacy.GenerationDisposition> generated(int least, String rows) {
        Compilation compilation = Compilation.ofSource(MODEL.formatted(least) + rows, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Offering offering = Adequacy.offeredFor(compilation.db(),
                OfferingRequest.overTheModule("example.quote"));
        List<Adequacy.GenerationDisposition> out = new ArrayList<>();
        offering.searched().values().forEach(filling -> out.addAll(filling.generation()));
        return out;
    }
}
