package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.TermPath;
import souther.compiler.observe.ObservedValue;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An element read alone answers for the element and could not walk anywhere else: not to the
 * container it is in, not to the container's other elements, not to another position.
 *
 * <p>What the most a count of a set's elements comes to is read off. A statement reading the
 * container — how many it holds, which of its elements is last to hold a value — or anything else
 * of the row would be answered by whatever a row holding the element wrote there; told it could
 * not walk there, it is told it could not tell, and a value is counted unless the statement fails
 * of it with nothing else known.
 */
class AnElementReadAloneIsToldNothingElseTest {

    private static final String MODEL = """
            module p
            data Flags = { c: Bool, n: Bool }
            data Bag = { items: Set<Flags>, limit: Int }
            behavior f : (o: Bag, b: Bool) -> Int
            let f (o, b) = if Set.size(o.items) == 1 then 1 else 2
            """;

    private static final TypeSymbol FLAGS = TypeSymbols.declared(new TypeKey("p", "Flags"));

    private static final TermPath ITEMS = TermPath.of("o").then("items");

    @Test
    void theElementIsWalkedAndNothingBesideIt() {
        BorderQuantity.Observation alone = aloneOf(new ObservedValue.Constructed(FLAGS,
                Map.of("c", new ObservedValue.Bool(false), "n", new ObservedValue.Bool(true))));

        assertEquals(WalkResult.reached(new ObservationAtPoint.Value(new ObservedValue.Bool(true))),
                alone.at(ITEMS.element().then("n")));
        for (TermPath beside : List.of(ITEMS, TermPath.of("o").then("limit"), TermPath.of("o"),
                TermPath.of("b"))) {
            assertEquals(WalkResult.couldNotWalk(), alone.at(beside), beside.toString());
            assertEquals(WalkResult.couldNotWalk(), alone.everyValueAt(beside),
                    beside.toString());
        }
        assertEquals(WalkResult.couldNotWalk(), alone.eachElementOf(ITEMS));
        assertTrue(alone.lastToHold(ITEMS, ITEMS.element().then("n"))
                instanceof BorderQuantity.Lastness.CouldNotTell);
    }

    private static BorderQuantity.Observation aloneOf(ObservedValue value) {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        RuleReadingContext reading = RuleReadingContext.unshared(
                RuleReadings.of(compilation, "p"), ReadAs.THE_COMPILATION_DOES);
        ElementValues values = ElementValues.of(ITEMS, Type.ref(FLAGS), reading, _ -> null);
        assertNotNull(values, "every part of the element is listed");
        return values.alone(value);
    }
}
