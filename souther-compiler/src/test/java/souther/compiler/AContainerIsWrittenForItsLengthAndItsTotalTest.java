package souther.compiler;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.GeneratedRows;

import org.junit.jupiter.api.Test;

import java.util.Arrays;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A location asked for how many it holds and for what it comes to is written once, holding that
 * many and coming to that.
 *
 * <p>Neither number is a place in the spelling of a list, and neither is read off a value the other
 * asks for: a list is composed out of both. So what a row writes there is a container of a size the
 * first number leaves, filled so that its elements come to the second — and a row written for one
 * of them and offered for both is a row that turns back at whichever guard the other is in.
 *
 * <p>Which is why the classes are read off the block below rather than counted. A row that fills
 * the class of the length and the class of the total is a row that answers both, and the page says
 * which classes each row it offers is for.
 */
class AContainerIsWrittenForItsLengthAndItsTotalTest {

    /**
     * A length and a total of one list, cut by one decision.
     *
     * <p>Both in one condition rather than one above the other, so that neither is on the way to
     * the other's points. Written as two guards, the length would reach the total's points as
     * something the row had to pass to get there — and a container filled against the way alone
     * would come out right without anything having asked the group.
     */
    private static final String A_LENGTH_AND_A_TOTAL = """
            module example.ledger

            data Yes = { v: Int }
            data No = { why: Int }

            behavior post : (ns: List<Int>) -> Yes | No
                constructs Yes
                constructs No

            let post (ns) =
                if List.length(ns) >= 2 && List.sum(ns) >= 10
                    then Yes { v = 1 } else No { why = 0 }
            """;

    /** The sentence a group nothing here writes a value for comes back as, which this is not. */
    private static final String THE_POPULATION =
            "the values that answer several of their own numbers";

    /**
     * Every class of both numbers is offered a row, and nothing says the group is one this compiler
     * writes none of.
     */
    @Test
    void aContainerIsComposedForBothOfItsNumbers() {
        String offered = block(measured(A_LENGTH_AND_A_TOTAL));

        assertFalse(offered.contains(THE_POPULATION),
                () -> "a container is composed out of its length and its total: " + offered);
        assertEquals(List.of(),
                offered.lines().filter(line -> line.contains("no row for")).toList(),
                () -> "so no class of either number is left without one: " + offered);
        assertTrue(offered.contains("| ("),
                () -> "and rows are offered: " + offered);
    }

    /**
     * And a row offered at a class of one number is a row that answers the other.
     *
     * <p>Read off what the page says each row fills, because the two numbers are of one location: a
     * row put at the class of the total while holding fewer elements than the length asks for is a
     * row nothing would catch here, and the author pasting it would meet the guard above the line.
     */
    @Test
    void theRowOfferedAtAClassOfOneNumberAnswersTheOtherAsWell() {
        String offered = block(measured(A_LENGTH_AND_A_TOTAL));

        String row = offered.lines().filter(line -> line.contains("\"ns=2 <= x\"")).findFirst()
                .orElseThrow(() -> new AssertionError(
                        "a row is offered at the class of two or more elements: " + offered));
        List<Integer> held = elementsOf(row);

        assertTrue(held.size() >= 2,
                () -> "and it holds that many, which is what the class it is labelled for is: "
                        + row);
        assertTrue(held.stream().mapToInt(Integer::intValue).sum() < 10,
                () -> "and comes to what the other number's class asks of it: " + row);
    }

    /** The numbers a written row holds, which is what the container it offers comes to. */
    private static List<Integer> elementsOf(String row) {
        String held = row.substring(row.indexOf('[') + 1, row.indexOf(']'));
        return held.isBlank() ? List.of()
                : Arrays.stream(held.split(",")).map(String::trim).map(Integer::valueOf).toList();
    }

    private static Compilation measured(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        return compilation;
    }

    private static String block(Compilation compilation) {
        return GeneratedRows.of(
                Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule("example.ledger")),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()),
                compilation.db()).text();
    }
}
