package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.check.NewtypeInners;
import souther.compiler.check.Symbols;
import souther.compiler.inputs.Case;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.ElementProjection;
import souther.compiler.inputs.ElementValue;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A total of what a walk computed of each element is read one element at a time, with the fields of
 * an element standing together.
 *
 * <p>The term and its orders are built by hand, so what is held here is the reading and the
 * identity of the number and not the walk that finds one in a body. What the reading owes is the
 * program's own answer: the numbers computed of the elements are added up, each computed the way the
 * program computes it, and an element the program stops at leaves the row no total.
 */
class ARunComputedOfEachElementIsReadOneElementAtATimeTest {

    private static final TermPath ELEMENTS = TermPath.of("xs").element();
    private static final ElementProjection Q = ElementProjection.ofFields(List.of("q"));
    private static final ElementProjection P = ElementProjection.ofFields(List.of("p"));
    private static final ElementProjection DEBIT = ElementProjection.ofFields(List.of("debit"));

    private static ElementValue form(ExactRatio constant, Map<ElementProjection, ExactRatio> weights) {
        return new ElementValue.Affine(new LinearForm<>(constant, weights));
    }

    private static NumericTerm.TakenOver total(ElementValue computation) {
        return NumericTerm.TakenOver.of(ValueName.Stdlib.operation("List", "sum"),
                new RunSource.ComputedOccurrences(ELEMENTS, computation, Type.Prim.INT),
                Type.Prim.INT, NewtypeInners.NONE,
                Symbols.none(souther.compiler.DefaultStdlib.get()));
    }

    private static TermOrders ordersOf(NumericTerm term, ElementProjection... fields) {
        Map<ElementProjection, Carrier> read = new HashMap<>();
        for (ElementProjection each : fields) {
            read.put(each, new Carrier.Whole());
        }
        return TermOrdersFixtures.computed(term, new Carrier.Whole(), new Carrier.Whole(), read);
    }

    /** One element's fields, as the row holds them. */
    private static Function<ElementProjection, ObservedValue> element(long q, long p) {
        Map<ElementProjection, ObservedValue> fields = Map.of(Q, new ObservedValue.Integer(q),
                P, new ObservedValue.Integer(p), DEBIT, new ObservedValue.Bool(q < 0));
        return fields::get;
    }

    private static Count number(NumericTerm.Reading read) {
        return (Count) assertInstanceOf(NumericTerm.Reading.Number.class, read).value();
    }

    /** Each element is computed and the results are added: the twice of each, not twice the sum. */
    @Test
    void theNumbersComputedOfTheElementsAreAddedUp() {
        NumericTerm.TakenOver twice = total(form(ExactRatio.ZERO, Map.of(Q, ExactRatio.of(2))));
        assertEquals(Count.of(6), number(ordersOf(twice, Q)
                .readOverElements(List.of(element(1, 0), element(2, 0)))));
    }

    /** What stands beside the field is added once for every element, and not once for the run. */
    @Test
    void aConstantBesideTheFieldIsAddedForEveryElement() {
        NumericTerm.TakenOver more = total(form(ExactRatio.ONE, Map.of(Q, ExactRatio.ONE)));
        TermOrders orders = ordersOf(more, Q);
        assertEquals(Count.of(0 + 1 + 2 + 3), number(orders.readOverElements(
                List.of(element(0, 0), element(1, 0), element(2, 0)))), "three elements, three ones");
        assertEquals(Count.of(0), number(orders.readOverElements(List.of())),
                "and a run of none comes to what the walk starts from, whatever is beside the field");
    }

    /** The fields of one element are read together: another element's value is never paired. */
    @Test
    void theFieldsOfOneElementAreReadTogether() {
        NumericTerm.TakenOver both = total(form(ExactRatio.ZERO,
                Map.of(Q, ExactRatio.ONE, P, ExactRatio.of(100))));
        assertEquals(Count.of(1 * 1 + 100 * 10 + 2 * 1 + 100 * 20),
                number(ordersOf(both, Q, P).readOverElements(
                        List.of(element(1, 10), element(2, 20)))));
    }

    /** An element the program stops at is no number: the total of the rest is not the program's. */
    @Test
    void anElementTheProgramStopsAtLeavesTheRowNoTotal() {
        long half = Long.MAX_VALUE / 2 + 1;
        NumericTerm.TakenOver twice = total(form(ExactRatio.ZERO, Map.of(Q, ExactRatio.of(2))));
        TermOrders orders = ordersOf(twice, Q);

        assertInstanceOf(NumericTerm.Reading.NotNumber.class,
                orders.readOverElements(List.of(element(half, 0), element(-half, 0))),
                "twice a number past half the range is past the range, though the two cancel: the"
                        + " program's own total would have stopped at the first of them");
        NumericTerm.TakenOver plain = total(form(ExactRatio.ZERO, Map.of(Q, ExactRatio.ONE)));
        assertEquals(Count.of(0), number(ordersOf(plain, Q)
                        .readOverElements(List.of(element(half, 0), element(-half, 0)))),
                "while the total of the numbers themselves is the number the program returns");
    }

    /** A choice by a flag the element holds is made for each element on its own. */
    @Test
    void aChoiceByAFlagIsMadeForEachElement() {
        ElementValue signed = new ElementValue.Choose(DEBIT,
                form(ExactRatio.ZERO, Map.of(Q, ExactRatio.of(-1))),
                form(ExactRatio.ZERO, Map.of(Q, ExactRatio.ONE)));
        // The flag is set where q is negative, so the first two are negated and the third is not.
        assertEquals(Count.of(1 + 2 + 3), number(ordersOf(total(signed), Q, DEBIT)
                .readOverElements(List.of(element(-1, 0), element(-2, 0), element(3, 0)))));
    }

    /**
     * A field only the branch not taken reads is not asked for.
     *
     * <p>What the row holds there, or fails to, says nothing about an element whose own choice
     * does not reach it.
     */
    @Test
    void aFieldTheChoiceDoesNotReachIsNotAskedFor() {
        ElementValue chosen = new ElementValue.Choose(DEBIT,
                form(ExactRatio.ZERO, Map.of(Q, ExactRatio.ONE)),
                form(ExactRatio.ZERO, Map.of(P, ExactRatio.ONE)));
        TermOrders orders = ordersOf(total(chosen), Q, P, DEBIT);

        Map<ElementProjection, ObservedValue> taken = Map.of(DEBIT, new ObservedValue.Bool(true),
                Q, new ObservedValue.Integer(3));
        Function<ElementProjection, ObservedValue> asked = field -> {
            assertNotEquals(P, field, "the flag is set, so the field the other branch reads is not"
                    + " asked for");
            return taken.get(field);
        };
        assertEquals(Count.of(3), number(orders.readOverElements(List.of(asked))),
                "and what the row holds there, or fails to, does not matter");

        Map<ElementProjection, ObservedValue> other = Map.of(DEBIT, new ObservedValue.Bool(false),
                Q, new ObservedValue.Integer(3));
        assertInstanceOf(NumericTerm.Reading.NotNumber.class,
                orders.readOverElements(List.of(other::get)),
                "while with the flag clear it is the field that was never written that is needed");
    }

    private static final TypeSymbol A = TypeSymbols.declared(new TypeKey("probe", "A"));
    private static final TypeSymbol B = TypeSymbols.declared(new TypeKey("probe", "B"));
    private static final TypeSymbol C = TypeSymbols.declared(new TypeKey("probe", "C"));
    private static final ElementProjection THE_ELEMENT = new ElementProjection(List.of());
    private static final ElementProjection AT_A = narrowedTo(A);
    private static final ElementProjection AT_B = narrowedTo(B);
    private static final ElementProjection A_AMOUNT = AT_A.then("amount");
    private static final ElementProjection B_AMOUNT = AT_B.then("amount");

    private static ElementProjection narrowedTo(TypeSymbol leaf) {
        return new ElementProjection(List.of(new TermPath.Step.Refine(
                CasesLeft.of(Refinement.of(new Case.SumCase(leaf, true))))));
    }

    /** {@code match d with | A { amount } -> amount | B { amount } -> amount * 10}. */
    private static final ElementValue BY_CASE = new ElementValue.OfItsCase(List.of(
            new ElementValue.OfItsCase.Arm(AT_A,
                    form(ExactRatio.ZERO, Map.of(A_AMOUNT, ExactRatio.ONE))),
            new ElementValue.OfItsCase.Arm(AT_B,
                    form(ExactRatio.ZERO, Map.of(B_AMOUNT, ExactRatio.of(10))))), null);

    private static ObservedValue ofCase(TypeSymbol leaf, long amount) {
        return new ObservedValue.Constructed(leaf, Map.of("amount", new ObservedValue.Integer(amount)));
    }

    /**
     * A choice by case is made for each element on its own, and each element's field is read under
     * its own case: two cases' fields of one name are two places.
     */
    @Test
    void aChoiceByCaseIsMadeForEachElement() {
        assertNotEquals(A_AMOUNT, B_AMOUNT);
        TermOrders orders = ordersOf(total(BY_CASE), A_AMOUNT, B_AMOUNT);
        List<Function<ElementProjection, ObservedValue>> each = new ArrayList<>();
        for (ObservedValue element : List.of(ofCase(A, 4), ofCase(B, 7), ofCase(A, 1))) {
            each.add(field -> field.in(element));
        }
        assertEquals(Count.of(4 + 70 + 1), number(orders.readOverElements(each)));
    }

    /**
     * The case is asked of the value it is the case of, and then only the fields of the arm that
     * took it.
     *
     * <p>Asked at a field of another case, an element holds nothing there, and a reading that
     * asked would take the element for one with nothing written where the computation looked.
     */
    @Test
    void theCaseIsAskedOfTheValueAndOnlyTheTakenArmsFieldsAfterIt() {
        TermOrders orders = ordersOf(total(BY_CASE), A_AMOUNT, B_AMOUNT);
        ObservedValue element = ofCase(B, 7);
        Function<ElementProjection, ObservedValue> asked = field -> {
            assertTrue(field.equals(THE_ELEMENT) || field.equals(B_AMOUNT),
                    () -> "a B is asked its case and its own amount, and not " + field);
            return field.in(element);
        };
        assertEquals(Count.of(70), number(orders.readOverElements(List.of(asked))));
    }

    /** A field of one case is nothing in a value of another, though the other has a field of that
     *  name. */
    @Test
    void aFieldOfOneCaseIsNothingInAValueOfAnother() {
        assertEquals(new ObservedValue.Integer(7), B_AMOUNT.in(ofCase(B, 7)));
        assertNull(A_AMOUNT.in(ofCase(B, 7)));
    }

    /** An element whose case was not read is no element any arm is guessed for. */
    @Test
    void anElementWhoseCaseWasNotReadTakesNoArm() {
        TermOrders orders = ordersOf(total(BY_CASE), A_AMOUNT, B_AMOUNT);
        ObservedValue unread = new ObservedValue.Unknown("not decoded");
        assertInstanceOf(NumericTerm.Reading.Missing.class,
                orders.readOverElements(List.of(field -> field.in(unread))));
    }

    /** An element of a case no arm takes is an element of another shape than the walk's. */
    @Test
    void anElementOfACaseNoArmTakesIsNoNumber() {
        TermOrders orders = ordersOf(total(BY_CASE), A_AMOUNT, B_AMOUNT);
        ObservedValue other = ofCase(C, 3);
        assertInstanceOf(NumericTerm.Reading.NotNumber.class,
                orders.readOverElements(List.of(field -> field.in(other))));
    }

    /** A number the exact arithmetic could not hold is said as that, and not as a value missing. */
    @Test
    void aNumberTheArithmeticCannotHoldIsNotAMissingValue() {
        // A number and a constant spaced as far apart in scale as the arithmetic is asked to add.
        BigDecimal huge = BigDecimal.ONE.scaleByPowerOfTen(Integer.MAX_VALUE - 10);
        BigDecimal tiny = BigDecimal.ONE.scaleByPowerOfTen(-(Integer.MAX_VALUE - 10));
        NumericTerm.TakenOver wide =
                total(form(ExactRatio.of(tiny), Map.of(Q, ExactRatio.ONE)));
        TermOrders orders = TermOrdersFixtures.computed(wide, new Carrier.Dense(),
                new Carrier.Dense(), Map.of(Q, new Carrier.Dense()));

        Map<ElementProjection, ObservedValue> element = Map.of(Q, new ObservedValue.Decimal(huge));
        assertInstanceOf(NumericTerm.Reading.NotWorkedOut.class,
                orders.readOverElements(List.of(element::get)),
                "the sum is past what the exact arithmetic writes, which is not a row missing a"
                        + " field");
    }

    /** What makes two of these one number is the computation as well as the elements. */
    @Test
    void twoComputationsOverOneListAreTwoNumbers() {
        NumericTerm.TakenOver twice = total(form(ExactRatio.ZERO, Map.of(Q, ExactRatio.of(2))));
        NumericTerm.TakenOver thrice = total(form(ExactRatio.ZERO, Map.of(Q, ExactRatio.of(3))));
        assertNotEquals(twice, thrice);
        assertEquals(twice, total(form(ExactRatio.ZERO, Map.of(Q, ExactRatio.of(2)))),
                "and one computation written twice is one number");
        assertNotEquals(twice.toString(), thrice.toString(),
                "which a form is walked and filed by, so they may not be written alike");
    }

    /** The values of a run gathered apart from their elements are not what this is read from. */
    @Test
    void valuesGatheredApartFromTheirElementsAreRefused() {
        NumericTerm.TakenOver twice = total(form(ExactRatio.ZERO, Map.of(Q, ExactRatio.of(2))));
        assertThrows(IllegalArgumentException.class,
                () -> ordersOf(twice, Q).readOver(List.of(new ObservedValue.Integer(1))));
    }
}
