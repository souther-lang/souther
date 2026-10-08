package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.semantics.ArgumentRef;
import souther.compiler.semantics.BuiltFrom;
import souther.compiler.semantics.ElementLineage;
import souther.compiler.semantics.MapPart;
import souther.compiler.semantics.OperationFact;
import souther.compiler.semantics.OperationFacts;
import souther.compiler.semantics.SizeAgainstItsSource;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A fact that relates what an operation answers to one of its arguments is held to that relation,
 * and not to each of the two alone.
 *
 * <p>A list and a map are each a container, and a map's keys and a list of its values are each of
 * some type — so holding each position to a requirement of its own lets through a fact that relates
 * them in no way the signature does. What is held here is the relation each kind of fact states,
 * over a declaration of the language with one fact put wrong.
 */
class AFactRelatingTheAnswerToAnArgumentIsHeldToThatRelationTest {

    private static final ValueName MAP_KEYS = ValueName.Stdlib.operation("Map", "keys");
    private static final ValueName MAP_VALUES = ValueName.Stdlib.operation("Map", "values");
    private static final ValueName LIST_MAP = ValueName.Stdlib.operation("List", "map");
    private static final ValueName LIST_LENGTH = ValueName.Stdlib.operation("List", "length");

    /** A list of a map's values is not a list of its keys. */
    @Test
    void aListOfOnePartOfAMapIsNotAListOfAnother() {
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> bindWith(MAP_VALUES, OperationFact.ListsAPartOf.class,
                        new OperationFact.ListsAPartOf(new ArgumentRef.At(0), MapPart.KEYS)));
        assertTrue(e.getMessage().contains("Map.values")
                && e.getMessage().contains("a list of the keys"), e.getMessage());

        IllegalStateException entries = assertThrows(IllegalStateException.class,
                () -> bindWith(MAP_KEYS, OperationFact.ListsAPartOf.class,
                        new OperationFact.ListsAPartOf(new ArgumentRef.At(0), MapPart.ENTRIES)));
        assertTrue(entries.getMessage().contains("a list of the entries"), entries.getMessage());
    }

    /** What answers no map keeps no keys, whatever it was given. */
    @Test
    void keysAreKeptOnlyByAMapKeyedLikeTheOneGiven() {
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> bindWith(MAP_VALUES, OperationFact.KeepsTheKeysOf.class,
                        new OperationFact.KeepsTheKeysOf(new ArgumentRef.At(0))));
        assertTrue(e.getMessage().contains("a map keyed by the keys of that map"),
                e.getMessage());
    }

    /** An answer of what a closure made is not one holding the very elements it was given. */
    @Test
    void anAnswerHoldingTheElementsOfAnArgumentHoldsValuesOfTheirType() {
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> bindWith(LIST_MAP, OperationFact.BuildsItsResultFrom.class,
                        new OperationFact.BuildsItsResultFrom(new BuiltFrom<>(
                                new ElementLineage.SameAs<>(
                                        new ElementLineage.Source<>(new ArgumentRef.TheContainer(),
                                                1)),
                                SizeAgainstItsSource.SAME))));
        assertTrue(e.getMessage().contains("List.map")
                && e.getMessage().contains("a container of the elements that argument holds"),
                e.getMessage());
    }

    /** A number is no smaller than nothing a container holds: a size is what is compared. */
    @Test
    void whatIsNoSmallerThanAContainerIsOne() {
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> bindWith(LIST_LENGTH, OperationFact.ResultIsNoSmallerThan.class,
                        new OperationFact.ResultIsNoSmallerThan(new ArgumentRef.At(0))));
        assertTrue(e.getMessage().contains("List.length")
                && e.getMessage().contains("what is no smaller than a container"),
                e.getMessage());
    }

    /**
     * The binding over the declarations the language has, with whatever {@code operation} says of
     * the kind {@code replacing} taken out and {@code fact} said instead.
     */
    private static void bindWith(ValueName operation, Class<? extends OperationFact> replacing,
                                 OperationFact fact) {
        List<OperationFacts.Declared> declared = new ArrayList<>();
        for (OperationFacts.Declared each : OperationFacts.declarations()) {
            if (!(each.operation().equals(operation) && replacing.isInstance(each.fact()))) {
                declared.add(each);
            }
        }
        declared.add(new OperationFacts.Declared(operation, fact));
        OperationFactBinder.bindAll(DefaultStdlib.get(), declared);
    }
}
