package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.TypeCardinality;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.observe.ObservedValue;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;
import souther.runtime.ConstraintViolation;
import souther.runtime.Lists;

import java.math.BigDecimal;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * What the elements of a key come to is read for every element of the run, whichever of them
 * could not be read, and a total is the number a run comes to where it answers.
 *
 * <p>An element whose key is not read may be of any key, so every element's reading stops there —
 * and every element has one: a reading that answers for some of the elements reads to a caller as
 * the others having no number at all, which is a definite answer this never had.
 *
 * <p>A total is read as the library's total answers: the numbers added up, and no number where
 * the total, or one element's number, is past what the program holds. Not each sum on the way: the
 * library adds wider on the way, and a walk adding with the operator, which stops where a sum on
 * the way is past it, is a run that does not answer — which running the row says, and no reading
 * of its elements does.
 */
class WhatTheElementsOfAKeyComeToIsReadForEveryElementTest {

    private static final String SOURCE = """
            module example.ledger

            data Posting = { account: String, amount: Int }

            data Taken

            behavior take : (ps: List<Posting>) -> Taken
            """;

    private static final ElementProjection ACCOUNT = ElementProjection.ofFields(
            List.of("account"));

    private static final ElementProjection AMOUNT = ElementProjection.ofFields(List.of("amount"));

    @Test
    void anElementWhoseKeyIsNotReadStopsTheReadingOfEveryElementWhereverItStands() {
        TermOrders on = quantities().ordersOf(totalOf(0));
        Function<ElementProjection, ObservedValue> unread = posting(
                new ObservedValue.Unknown("not read"), 3);
        Function<ElementProjection, ObservedValue> read = posting(new ObservedValue.Text("a"), 3);
        for (List<Function<ElementProjection, ObservedValue>> elements : List.of(
                List.of(unread, read, read), List.of(read, unread, read),
                List.of(read, read, unread))) {
            List<NumericTerm.Reading> each = on.readEachUnderItsKey(elements);
            assertEquals(elements.size(), each.size(), "one reading for every element");
            each.forEach(reading -> assertInstanceOf(NumericTerm.Reading.Missing.class, reading,
                    "what stopped the key is what every element is told"));
        }
    }

    /**
     * A key's total past the last number an {@code Int} holds is none; one that comes back to it
     * is that number, whatever order its elements stand in — a walk handed them so that a sum on
     * the way passes it is a run that stops, which running the row says.
     */
    @Test
    void aKeysTotalIsNoNumberOnlyWherePastWhatTheProgramHolds() {
        TermOrders on = quantities().ordersOf(totalOf(0));
        assertInstanceOf(NumericTerm.Reading.NotNumber.class, on.readEachUnderItsKey(List.of(
                posting("a", Long.MAX_VALUE), posting("a", 1))).getFirst());
        for (List<Long> amounts : List.of(List.of(Long.MAX_VALUE, 1L, -1L),
                List.of(-1L, 1L, Long.MAX_VALUE), List.of(Long.MAX_VALUE - 1, 1L))) {
            assertEquals(new NumericTerm.Reading.Number(count(Long.MAX_VALUE)),
                    on.readEachUnderItsKey(amounts.stream().map(each -> posting("a", each))
                            .toList()).getFirst(), amounts::toString);
        }
    }

    /**
     * A number one element is made into, past what the program holds, is none either — though
     * the element before it brings the running sum back: the program stopped making the number,
     * before any adding.
     */
    @Test
    void anElementsNumberPastWhatTheProgramHoldsIsNoNumber() {
        TermOrders on = quantities().ordersOf(totalOf(1));
        assertInstanceOf(NumericTerm.Reading.NotNumber.class, on.readEachUnderItsKey(List.of(
                posting("a", -6), posting("a", Long.MAX_VALUE))).getFirst());
    }

    /**
     * A total over a list reads what the library's total answers, held against the run time's own
     * {@code List.sum}: the number where it comes to one, though a sum on the way passes the last
     * number, and none where it aborts.
     */
    @Test
    void aTotalOverAListIsWhatTheLibrarysTotalAnswers() {
        Compilation compilation = Compilation.ofSource(SOURCE, "Main");
        RuleReadingSource rules = RuleReadings.of(compilation, compilation.modules().get(0));
        NumericTerm total = NumericTerm.TakenOver.of(ValueName.Stdlib.operation("List", "sum"),
                RunSource.overTheOccurrencesAt(AMOUNT.from(TermPath.of("ps").element())),
                Type.Prim.INT, rules.inners(), rules.symbols());
        TermOrders on = quantities().ordersOf(total);
        for (List<Long> values : List.of(List.of(Long.MAX_VALUE, 1L, -1L),
                List.of(-1L, 1L, Long.MAX_VALUE), List.of(Long.MAX_VALUE, -1L, 1L),
                List.of(Long.MAX_VALUE, 1L))) {
            NumericTerm.Reading read = on.readOver(values.stream()
                    .<ObservedValue>map(ObservedValue.Integer::new).toList());
            NumericTerm.Reading ran;
            try {
                ran = new NumericTerm.Reading.Number(count(Lists.sumInt(values)));
            } catch (ConstraintViolation aborted) {
                ran = new NumericTerm.Reading.NotNumber();
            }
            assertEquals(ran, read, values::toString);
        }
    }

    private static Function<ElementProjection, ObservedValue> posting(String account,
                                                                     long amount) {
        return posting(new ObservedValue.Text(account), amount);
    }

    private static Function<ElementProjection, ObservedValue> posting(ObservedValue account,
                                                                     long amount) {
        return field -> field.equals(ACCOUNT) ? account : new ObservedValue.Integer(amount);
    }

    private static Count count(long at) {
        return new Count(BigDecimal.valueOf(at));
    }

    /** The total under the account of {@code amount + added}. */
    private static NumericTerm totalOf(int added) {
        return NumericTerm.GatheredUnderItsKey.of(TermPath.of("ps").element(), ACCOUNT,
                new ElementValue.Affine(new LinearForm<>(ExactRatio.of(added),
                        Map.of(AMOUNT, ExactRatio.ONE))),
                Type.Prim.INT, NumericTerm.GatheredUnderItsKey.Gathering.TOTAL);
    }

    private static Quantities quantities() {
        Compilation compilation = Compilation.ofSource(SOURCE, "Main");
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext reading =
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES);
        return InputDomain.of(sigs.get("take"), reading,
                        TypeCardinality.Counts.workedOutIn(reading),
                        souther.compiler.carrier.Membership.none())
                .quantities(rules);
    }
}
