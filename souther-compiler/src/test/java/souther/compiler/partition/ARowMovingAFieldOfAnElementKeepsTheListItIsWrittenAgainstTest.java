package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A row moving a field under {@code [*]} is the list the model states with that field moved in
 * every element, and not a list built again from the classes.
 *
 * <p>A position under {@code [*]} is a position of each element, so the edit is made to each of
 * them and the rest of every element stays what the model put there — the way a spread keeps the
 * rest of a record. Built again from the classes, the list became one element at the first class
 * of each of its other positions, and a body reading those positions saw a value nobody wrote.
 */
class ARowMovingAFieldOfAnElementKeepsTheListItIsWrittenAgainstTest {

    private static final String MODEL = """
            module example.items

            data Self
            data Company
            data Payer = Self | Company

            data Item = { amount: Int, payer: Payer }

            data Sum = { n: Int }

            behavior total : (items: List<Item>) -> Sum
                constructs Sum

            let total (items) = Sum { n = List.fold((acc, i) -> acc + i.amount, 0, items) }

            let train = Item { amount = 3000, payer = Self }

            let hotel = Item { amount = 12000, payer = Self }

            """;

    /** The list is named and the moved field is written over each of its elements. */
    @Test
    void theMovedFieldIsWrittenOverEveryElementOfTheNamedList() {
        assertEquals(List.of("List.map(items -> Item { ...items, payer = Company }, trip)"),
                rowsOf(MODEL + """
                        let trip: List<Item> = [ train, hotel ]

                        example total
                            | "the trip" : (trip) -> Sum { n = 15000 }
                        """));
    }

    /**
     * And where the list stands at two classes of the position at once, the row still names it.
     * Each element is classified on its own, so the list is in both classes, and what is moved is
     * moved in every element.
     */
    @Test
    void aListStandingAtTwoClassesOfThePositionIsStillTheBaseline() {
        List<String> rows = rowsOf("""
                module example.items

                data Self
                data Company
                data Advance
                data Payer = Self | Company | Advance

                data Item = { amount: Int, payer: Payer }

                data Sum = { n: Int }

                behavior total : (items: List<Item>) -> Sum
                    constructs Sum

                let total (items) = Sum { n = List.fold((acc, i) -> acc + i.amount, 0, items) }

                let train = Item { amount = 3000, payer = Self }

                let hotel = Item { amount = 12000, payer = Company }

                let trip: List<Item> = [ train, hotel ]

                example total
                    | "the trip" : (trip) -> Sum { n = 15000 }
                """);
        assertEquals(List.of("List.map(items -> Item { ...items, payer = Advance }, trip)"), rows);
    }

    private static List<String> rowsOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, Adequacy.Filling> all = Adequacy.generatedOf(compilation.db(), "example.items");
        assertNotNull(all, "the model under test compiles");
        return all.get("total").composed().rows().stream()
                .map(row -> String.join(", ", row.inputs().stream().map(i -> i.text()).toList()))
                .toList();
    }
}
