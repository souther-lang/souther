package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.semantics.ArgumentRef;
import souther.compiler.semantics.ElementLineage;
import souther.compiler.semantics.OperationFact;
import souther.compiler.semantics.OperationFacts;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * That an operation's answer holds the image of every element of its source is held to the
 * signature, and for an operation the library writes it is proved of the body: a body that leaves
 * an element out is not that statement, however well it says where the elements it keeps came from.
 */
class AnImageOfEveryElementIsProvedOfTheBodyTest {

    private static final ValueName SET_MAP = ValueName.Stdlib.operation("Set", "map");
    private static final ValueName SET_FROM_LIST = ValueName.Stdlib.operation("Set", "fromList");
    private static final ValueName LIST_LENGTH = ValueName.Stdlib.operation("List", "length");

    private static final String SHIPPED_BODY =
            "Set.fold((acc, x) -> Set.insert(f(x), acc), Set.empty, s)";

    /** Control: what the library ships is proved, and said of the kernels as they are declared. */
    @Test
    void theLibraryAsShippedHoldsTheImageOfEveryElement() {
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();

        assertInstanceOf(ElementLineage.ClosureResult.class,
                facts.holdsTheImageOfEveryElement(SET_MAP),
                "a set made of what a closure answered holds every answer");
        assertInstanceOf(ElementLineage.SameAs.class,
                facts.holdsTheImageOfEveryElement(SET_FROM_LIST),
                "a set made of a list holds every value in it");
        assertNull(facts.holdsTheImageOfEveryElement(ValueName.Stdlib.operation("List", "filter")),
                "a filter leaves elements out");
    }

    /** A step that carries what it has where it would have put a value in leaves an element out. */
    @Test
    void aBodyThatMayPutNothingInIsNotProved() {
        BoundOperationFacts facts = proved(
                "Set.fold((acc, x) -> if Set.contains(f(x), acc) then acc"
                        + " else Set.insert(f(x), acc), Set.empty, s)");

        assertNull(facts.holdsTheImageOfEveryElement(SET_MAP));
        assertTrue(facts.notProvedOfTheirBodies().stream().anyMatch(
                each -> each instanceof BoundOperationFact.HoldsTheImageOfEveryElement
                        && each.operation().operation().equals(SET_MAP)),
                "stated, and left unproved rather than filed");
    }

    /** What is put in is the closure's answer on the element the walk is at and on no other. */
    @Test
    void aBodyThatPutsSomethingElseInIsNotProved() {
        BoundOperationFacts facts = proved(
                "Set.fold((acc, x) -> Set.insert(f(x), Set.insert(f(x), acc)), Set.empty, s)");

        assertNull(facts.holdsTheImageOfEveryElement(SET_MAP));
    }

    /** An operation taking no closure has no closure's answer to hold an image of. */
    @Test
    void anOperationTakingNoClosureHasNoClosureAnswerToHold() {
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> OperationFactBinder.bindAll(DefaultStdlib.get(), declarations(LIST_LENGTH,
                        new OperationFact.HoldsTheImageOfEveryElement(
                                new ElementLineage.ClosureResult<>(new ElementLineage.Source<>(
                                        new ArgumentRef.At(0), 1))))));
        assertTrue(e.getMessage().contains("List.length")
                && e.getMessage().contains("hands no closure"), e.getMessage());
    }

    /** Only the element itself or the closure's answer on it is an image. */
    @Test
    void whatIsInsideTheClosuresAnswerIsNoImage() {
        assertThrows(IllegalArgumentException.class,
                () -> new OperationFact.HoldsTheImageOfEveryElement(
                        new ElementLineage.InsideClosureResult<>(new ElementLineage.Source<>(
                                new ArgumentRef.TheContainer(), 1))));
    }

    private static List<OperationFacts.Declared> declarations(ValueName operation,
                                                              OperationFact with) {
        List<OperationFacts.Declared> declared = new ArrayList<>(OperationFacts.declarations());
        declared.add(new OperationFacts.Declared(operation, with));
        return declared;
    }

    /** The library as shipped with {@code Set.map} written as {@code body}, proved. */
    private static BoundOperationFacts proved(String body) {
        Stdlib stdlib = StdlibLoader.load(text -> text.contains(SHIPPED_BODY)
                ? text.replace(SHIPPED_BODY, body) : text);
        return OperationFactBinder.bindAll(stdlib);
    }
}
