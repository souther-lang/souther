package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.ACarriedValue;
import souther.compiler.meaning.CompoundSamples;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.OnOneElement;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The walks that ask whether a row can be asked a statement, or which numbers it names, go
 * through the kinds they name by the parts {@link Proposition#partsHeld} gives, and through no
 * other: what a statement over each of the applications of something, or over the nodes
 * reachable, holds is not a statement a row is asked because its parts are.
 *
 * <p>Each walk has its table, with every kind that holds statements placed in it. A kind added to
 * {@code Proposition} has to be placed before the test that reads the kinds off the class passes,
 * and a walk made to go into a kind it left fails where that kind is asked.
 */
class EachWalkOfARowMeetsTheKindsItNamesAndNoOtherTest {

    private static final Set<Class<?>> GONE_INTO = Set.of(
            Proposition.All.class, Proposition.Any.class, Proposition.WhereItAnswers.class,
            Proposition.SoManyHold.class, Proposition.OfTheWays.class, Proposition.Some.class);
    private static final Set<Class<?>> LEFT = Set.of(
            Proposition.OnAnApplication.class, Proposition.SomeReachable.class);

    private static final DecisionSubject CONTAINER = new DecisionSubject.AnInput(
            TermPath.of("xs"));

    private static final Proposition.Compared X = CompoundSamples.numberAtLeastZero("x");
    private static final Proposition.Compared Y = CompoundSamples.numberAtLeastZero("y");
    private static final Proposition UNREAD = CompoundSamples.unread(0);
    private static final Proposition ALSO_UNREAD = CompoundSamples.unread(1);

    private static Proposition around(Class<?> kind, Proposition one, Proposition other) {
        return CompoundSamples.holding(kind, one, other, CONTAINER);
    }

    private static Proposition written(Proposition ofTheWays) {
        return ((Proposition.OfTheWays) ofTheWays).written();
    }

    @Test
    void everyKindThatHoldsStatementsIsPlacedInTheTable() {
        Set<Class<?>> placed = new LinkedHashSet<>(GONE_INTO);
        placed.addAll(LEFT);
        assertEquals(new LinkedHashSet<Class<?>>(CompoundSamples.COMPOUNDS), placed);
        assertTrue(GONE_INTO.stream().noneMatch(LEFT::contains));
    }

    @Test
    void aRowIsAskedAStatementThroughTheKindsItNamesAndNoOther() {
        for (Class<?> kind : CompoundSamples.COMPOUNDS) {
            Proposition both = around(kind, X, Y);
            String named = kind.getSimpleName();
            if (kind == Proposition.OfTheWays.class) {
                assertEquals(AStatementAtARow.askable(written(both)),
                        AStatementAtARow.askable(both), named);
            } else {
                assertEquals(GONE_INTO.contains(kind), AStatementAtARow.askable(both), named);
            }
        }
    }

    @Test
    void aPartNoRowIsAskedKeepsTheKindsItIsGoneIntoFromBeingAsked() {
        for (Class<?> kind : GONE_INTO) {
            assertFalse(AStatementAtARow.askable(around(kind, UNREAD, ALSO_UNREAD)),
                    kind.getSimpleName());
            if (CompoundSamples.TWO_PARTS.contains(kind)) {
                assertFalse(AStatementAtARow.askable(around(kind, X, UNREAD)),
                        kind.getSimpleName());
                assertFalse(AStatementAtARow.askable(around(kind, UNREAD, X)),
                        kind.getSimpleName());
            }
        }
    }

    /** A statement left is not asked for the parts it holds being asked. */
    @Test
    void whatIsLeftIsNotAskedForItsPartsBeingAsked() {
        assertTrue(AStatementAtARow.askable(X));
        for (Class<?> kind : LEFT) {
            assertFalse(AStatementAtARow.askable(around(kind, X, Y)), kind.getSimpleName());
            assertFalse(AStatementAtARow.askable(
                    new Proposition.All(List.of(X, around(kind, X, Y)))), kind.getSimpleName());
        }
    }

    /** The parts are asked in order and the first that settles it ends the asking. */
    @Test
    void aJoinedStatementEndsWhereAPartSettlesIt() {
        Proposition carried = new Proposition.Carried(ACarriedValue.made(), true);
        assertFalse(AStatementAtARow.askable(new Proposition.All(List.of(UNREAD, carried))));
        assertFalse(AStatementAtARow.askable(new Proposition.Any(List.of(UNREAD, carried))));
        // The part ended at is what keeps it from being thrown for: asked, it is.
        assertThrows(IllegalStateException.class,
                () -> AStatementAtARow.askable(new Proposition.All(List.of(X, carried))));
    }

    private static final NumericTerm TERM_X = new NumericTerm.ValueOf(TermPath.of("x"));
    private static final NumericTerm TERM_Y = new NumericTerm.ValueOf(TermPath.of("y"));
    private static final Quantity.OfABinding ELEMENT = new Quantity.OfABinding(
            new BindingId(new BindingOwner.OfValue("demo", "f"), 0), List.of(), Type.INT,
            Optional.empty(), Optional.of(new Quantity.AWholeNumberInTurn(
                    LinearForm.constant(ExactRatio.ZERO),
                    new LinearForm<>(ExactRatio.ZERO, Map.of(TERM_X, ExactRatio.ONE)))));

    /** {@code element - x >= 0}: a statement of the element, which putting it at a value leaves
     *  as one of the input's number. */
    private static final Proposition ANCHOR = new Proposition.Compared(
            new Relation.Affine(new LinearForm<Quantity>(ExactRatio.ZERO, Map.of(
                    ELEMENT, ExactRatio.ONE,
                    new DecisionAtom.OfTheInput(TERM_X), ExactRatio.of(-1))), Rel.GE), true);

    /** {@code element - y >= 0}: a statement of the element that asking it without putting the
     *  element at a value cannot answer, so a kind that is asked the way a statement of the
     *  element is asked is told from one that is asked as it stands. */
    private static final Proposition OF_THE_ELEMENT = new Proposition.Compared(
            new Relation.Affine(new LinearForm<Quantity>(ExactRatio.ZERO, Map.of(
                    ELEMENT, ExactRatio.ONE,
                    new DecisionAtom.OfTheInput(TERM_Y), ExactRatio.of(-1))), Rel.GE), true);

    /** The anchor beside {@code part}: the element is found by the kinds that are looked into
     *  for it, and {@code part} is asked with the element put at a value. */
    private static Proposition besideTheElement(Proposition part) {
        return new Proposition.All(List.of(ANCHOR, part));
    }

    @Test
    void theElementOfTheStatementsIsFoundBeforeItIsAskedAtAValue() {
        assertTrue(OnOneElement.theElementOf(besideTheElement(Y)).isPresent());
        assertTrue(AStatementAtARow.askableAtSomeElement(besideTheElement(Y)));
    }

    @Test
    void aRowIsAskedAStatementAtAnElementThroughTheKindsItNamesAndNoOther() {
        for (Class<?> kind : CompoundSamples.COMPOUNDS) {
            Proposition stated = besideTheElement(around(kind, OF_THE_ELEMENT, X));
            assertTrue(OnOneElement.theElementOf(stated).isPresent(), kind.getSimpleName());
            if (kind == Proposition.OfTheWays.class) {
                assertEquals(AStatementAtARow.askableAtSomeElement(
                                besideTheElement(written(around(kind, OF_THE_ELEMENT, X)))),
                        AStatementAtARow.askableAtSomeElement(stated), kind.getSimpleName());
            } else {
                assertEquals(GONE_INTO.contains(kind),
                        AStatementAtARow.askableAtSomeElement(stated), kind.getSimpleName());
            }
        }
    }

    @Test
    void aPartNoRowIsAskedAtAnElementKeepsTheKindsItIsGoneIntoFromBeingAsked() {
        for (Class<?> kind : GONE_INTO) {
            assertFalse(AStatementAtARow.askableAtSomeElement(
                    besideTheElement(around(kind, UNREAD, ALSO_UNREAD))), kind.getSimpleName());
            if (CompoundSamples.TWO_PARTS.contains(kind)) {
                assertFalse(AStatementAtARow.askableAtSomeElement(
                        besideTheElement(around(kind, OF_THE_ELEMENT, UNREAD))), kind.getSimpleName());
                assertFalse(AStatementAtARow.askableAtSomeElement(
                        besideTheElement(around(kind, UNREAD, OF_THE_ELEMENT))), kind.getSimpleName());
            }
        }
    }

    @Test
    void theNumbersAreGatheredThroughTheKindsItNamesAndNoOther() {
        for (Class<?> kind : CompoundSamples.COMPOUNDS) {
            Proposition both = around(kind, X, Y);
            Set<NumericTerm> numbers = AStatementAtARow.numbersOf(both);
            String named = kind.getSimpleName();
            if (kind == Proposition.OfTheWays.class) {
                assertEquals(AStatementAtARow.numbersOf(written(both)), numbers, named);
                assertTrue(numbers.contains(TERM_X), named);
            } else if (LEFT.contains(kind)) {
                assertEquals(Set.of(), numbers, named);
            } else if (CompoundSamples.TWO_PARTS.contains(kind)) {
                assertEquals(List.of(TERM_X, TERM_Y), List.copyOf(numbers), named);
            } else {
                assertEquals(List.of(TERM_X), List.copyOf(numbers), named);
            }
        }
    }
}
