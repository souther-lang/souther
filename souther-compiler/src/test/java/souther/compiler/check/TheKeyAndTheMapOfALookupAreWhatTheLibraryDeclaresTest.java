package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.semantics.ArgumentRef;
import souther.compiler.semantics.OperationFact;
import souther.compiler.semantics.OperationFacts;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which argument of a lookup is the key and which is the map, and which argument of a put is the
 * key it files under, is what the library declares of the operation, and is read from there by
 * every reader of a lookup or a put — each of which was once handed the operation's name and the
 * places of its arguments.
 */
class TheKeyAndTheMapOfALookupAreWhatTheLibraryDeclaresTest {

    private static final SourcePos POS = new SourcePos(1, 1);
    private static final ValueName MAP_GET = ValueName.Stdlib.operation("Map", "get");
    private static final ValueName MAP_INSERT = ValueName.Stdlib.operation("Map", "insert");
    private static final ValueName LIST_GET = ValueName.Stdlib.operation("List", "get");

    /** Control: a map's lookup says its key and its map, a list's says neither, and what it
     *  answers is an element of the map as it is of the operations that state it alone. */
    @Test
    void aMapLookupSaysItsKeyAndItsMap() {
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();

        BoundOperationFacts.Lookup lookup = facts.looksUp(MAP_GET);
        assertNotNull(lookup);
        assertEquals(0, lookup.key().position());
        assertEquals(1, lookup.container().position());
        assertNull(facts.looksUp(LIST_GET), "an index is no key a container files a value under");
        assertEquals(1, facts.answersAnElementOf(MAP_GET).position(),
                "what a lookup answers is stated from where it looks, and not beside it");
    }

    /** A map's put says the key the value is filed under, and a set's, which has none, does not. */
    @Test
    void aMapPutSaysTheKeyItFilesUnder() {
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();

        BoundOperationFact.PutsAValueIn put = facts.putsAValueIn(MAP_INSERT);
        assertNotNull(put);
        assertEquals(0, put.under().orElseThrow().position());
        assertEquals(1, put.value().position());
        assertEquals(2, put.into().position());
        assertTrue(facts.putsAValueIn(ValueName.Stdlib.operation("Set", "insert")).under()
                .isEmpty());
    }

    /**
     * The greater of the two arguments of a comparison is the one the operation names, and not the
     * first: {@code compare(a, b)} is positive where {@code a} is the greater and
     * {@code daysBetween(a, b)} where {@code b} is, so a reader reading the sign against nought as
     * the order of the two as they were handed would read the second the wrong way round.
     */
    @Test
    void theGreaterOfTwoArgumentsIsTheOneTheOperationNames() {
        Core first = new Core.Int(1, Type.INT, POS);
        Core second = new Core.Int(2, Type.INT, POS);

        AnOperationApplied.Ordered compared = new AnOperationApplied(
                ValueName.Stdlib.operation("Decimal", "compare"), List.of(first, second))
                .ordersItsArguments();
        AnOperationApplied.Ordered between = new AnOperationApplied(
                ValueName.Stdlib.operation("Date", "daysBetween"), List.of(first, second))
                .ordersItsArguments();

        assertEquals(first, compared.greater());
        assertEquals(second, compared.lesser());
        assertEquals(second, between.greater());
        assertEquals(first, between.lesser());
        assertNull(new AnOperationApplied(MAP_GET, List.of(first, second)).ordersItsArguments(),
                "an operation that states no order is no comparison");
    }

    /** What widens a whole number is declared to answer the number of a whole number as it is,
     *  and an operation answering another kind of number as it is does not. */
    @Test
    void onlyAnOperationAnsweringAWholeNumberAsItIsWidensOne() {
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();

        assertTrue(facts.widensAWholeNumber(ValueName.Stdlib.operation("Decimal", "fromInt")));
        assertFalse(facts.widensAWholeNumber(ValueName.Stdlib.operation("Decimal", "add")));
        assertFalse(facts.widensAWholeNumber(MAP_GET));
    }

    /** What is said to be the key must be a key of what is said to file it. */
    @Test
    void aKeyThatIsNotAKeyOfTheMapIsRefused() {
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> OperationFactBinder.bindAll(DefaultStdlib.get(), List.of(
                        new OperationFacts.Declared(MAP_GET,
                                new OperationFact.AnswersTheValueFiledUnder(
                                        new ArgumentRef.At(1), new ArgumentRef.At(1))))));
        assertTrue(e.getMessage().contains("Map.get"), e.getMessage());
    }

    /** An operation the library writes in the language is read of its body, not declared. */
    @Test
    void aLookupIsNotDeclaredOfAWrittenOperation() {
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> OperationFactBinder.bindAll(DefaultStdlib.get(), List.of(
                        new OperationFacts.Declared(
                                ValueName.Stdlib.operation("Map", "updateIfPresent"),
                                new OperationFact.AnswersTheValueFiledUnder(
                                        new ArgumentRef.At(0), new ArgumentRef.At(2))))));
        assertTrue(e.getMessage().contains("Map.updateIfPresent"), e.getMessage());
    }
}
