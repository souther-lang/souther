package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.semantics.ArgumentRef;
import souther.compiler.semantics.BuiltFrom;
import souther.compiler.semantics.ElementLineage;
import souther.compiler.semantics.OperationFact;
import souther.compiler.semantics.OperationFacts;
import souther.compiler.semantics.SizeAgainstItsSource;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A statement that an element is what a closure answered is held to the signature of the operation
 * it is about, and for an operation the library writes it is proved of the body.
 *
 * <p>Said where the elements came from and not how many, as {@code List.flatMap} says it. The
 * binding is what keeps a lineage from naming a closure the operation does not take, and the proof
 * is what keeps the body from making something else. Each is held here by a declaration or a body
 * that is wrong, since what the library has is right and shows neither refuses anything.
 */
class AnElementsLineageIsHeldToTheSignatureAndProvedOfTheBodyTest {

    private static final ValueName FLAT_MAP = ValueName.Stdlib.operation("List", "flatMap");
    private static final ValueName FILTER_MAP = ValueName.Stdlib.operation("List", "filterMap");
    private static final ValueName FILTER = ValueName.Stdlib.operation("List", "filter");
    private static final ValueName LENGTH = ValueName.Stdlib.operation("List", "length");

    private static final ArgumentRef CONTAINER = new ArgumentRef.TheContainer();

    private static final String SHIPPED_BODY = "List.fold((acc, x) -> acc ++ f(x), [], xs)";

    private static ElementLineage<ArgumentRef> insideTheClosuresAnswer() {
        return new ElementLineage.InsideClosureResult<>(new ElementLineage.Source<>(CONTAINER, 1));
    }

    private static List<OperationFacts.Declared> declarations(
            ValueName without, Class<? extends OperationFact> kind, OperationFact with) {
        List<OperationFacts.Declared> declared = new ArrayList<>();
        for (OperationFacts.Declared each : OperationFacts.declarations()) {
            if (!(each.operation().equals(without) && kind.isInstance(each.fact()))) {
                declared.add(each);
            }
        }
        if (with != null) {
            declared.add(new OperationFacts.Declared(without, with));
        }
        return declared;
    }

    /**
     * An operation that takes no closure has no closure's answer for its elements to be in, however
     * the container is named. By place it passes every check of the argument alone — it is a list.
     */
    @Test
    void anOperationTakingNoClosureHasNoClosureAnswerToComeFrom() {
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> OperationFactBinder.bindAll(DefaultStdlib.get(), declarations(LENGTH,
                        OperationFact.ElementsComeFrom.class,
                        new OperationFact.ElementsComeFrom(
                                new ElementLineage.InsideClosureResult<>(
                                        new ElementLineage.Source<>(new ArgumentRef.At(0), 1))))));
        assertTrue(e.getMessage().contains("List.length")
                && e.getMessage().contains("hands no closure"), e.getMessage());
    }

    /** A building says it as much as a lineage declared alone does, so it is held as well. */
    @Test
    void aBuildingWhoseClosureAnswersSomethingElseIsRefused() {
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> OperationFactBinder.bindAll(DefaultStdlib.get(), declarations(FILTER,
                        OperationFact.BuildsItsResultFrom.class,
                        new OperationFact.BuildsItsResultFrom(new BuiltFrom<>(
                                new ElementLineage.ClosureResult<>(
                                        new ElementLineage.Source<>(CONTAINER, 1)),
                                SizeAgainstItsSource.AT_MOST)))));
        assertTrue(e.getMessage().contains("List.filter")
                && e.getMessage().contains("which are not what the result holds"),
                e.getMessage());
    }

    /** What a closure answered whole and what is inside it are not one lineage. */
    @Test
    void aListAnsweredIsNotTheElementItHolds() {
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> OperationFactBinder.bindAll(DefaultStdlib.get(), declarations(FLAT_MAP,
                        OperationFact.ElementsComeFrom.class,
                        new OperationFact.ElementsComeFrom(new ElementLineage.ClosureResult<>(
                                new ElementLineage.Source<>(CONTAINER, 1))))));
        assertTrue(e.getMessage().contains("List.flatMap")
                && e.getMessage().contains("which are not what the result holds"),
                e.getMessage());
    }

    /** Where the elements came from is said once: a building has said it. */
    @Test
    void anOperationWithABuildingIsNotAlsoToldWhereItsElementsCameFrom() {
        List<OperationFacts.Declared> declared = declarations(FILTER_MAP,
                OperationFact.ElementsComeFrom.class,
                new OperationFact.ElementsComeFrom(insideTheClosuresAnswer()));
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> OperationFactBinder.bindAll(DefaultStdlib.get(), declared));
        assertTrue(e.getMessage().contains("List.filterMap")
                && e.getMessage().contains("as a building and again alone"), e.getMessage());
    }

    /** Control: the body the library ships proves what is stated of it. */
    @Test
    void theBodyTheLibraryShipsProvesWhereItsElementsCameFrom() {
        BoundOperationFacts facts = OperationFactBinder.bindAll(DefaultStdlib.get());

        assertNotNull(facts.elementsMadeFromAlone(FLAT_MAP));
    }

    /** A closure applied to an element other than the one the walk is at is not that lineage. */
    @Test
    void aClosureAppliedToAnotherElementIsNotProved() {
        BoundOperationFacts facts = proved(
                "List.fold((acc, x) -> match List.get(0, xs) with"
                        + " | None -> acc | Some y -> acc ++ f(y), [], xs)");

        assertNull(facts.elementsMadeFromAlone(FLAT_MAP));
        assertTrue(facts.notProvedOfTheirBodies().stream().anyMatch(
                each -> each instanceof BoundOperationFact.ElementsComeFrom
                        && each.operation().operation().equals(FLAT_MAP)),
                "stated, and left unproved rather than filed");
    }

    /** What a body is shown to hold any number of is not shown to hold no more than it was given. */
    @Test
    void whatHoldsAnyNumberForEachElementIsNotProvedToHoldNoMore() {
        Stdlib stdlib = DefaultStdlib.get();
        BoundOperationFacts facts = OperationFactBinder.bindAll(stdlib, declarations(FLAT_MAP,
                OperationFact.ElementsComeFrom.class,
                new OperationFact.BuildsItsResultFrom(new BuiltFrom<>(insideTheClosuresAnswer(),
                        SizeAgainstItsSource.AT_MOST))));

        assertNull(facts.buildsItsResultFrom(FLAT_MAP));
        assertEquals(1, facts.notProvedOfTheirBodies().stream()
                .filter(each -> each instanceof BoundOperationFact.BuildsItsResultFrom
                        && each.operation().operation().equals(FLAT_MAP)).count());
    }

    /** The library as shipped with {@code flatMap} written as {@code body}, proved. */
    private static BoundOperationFacts proved(String body) {
        Stdlib stdlib = StdlibLoader.load(text -> {
            if (!text.contains(SHIPPED_BODY)) {
                return text;
            }
            return text.replace(SHIPPED_BODY, body);
        });
        return OperationFactBinder.bindAll(stdlib);
    }
}
