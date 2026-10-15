package souther.compiler.inputs;

import org.junit.jupiter.api.Test;
import souther.compiler.DefaultStdlib;
import souther.compiler.check.Carrier;
import souther.compiler.check.ScopedDeclarations;
import souther.compiler.check.Symbols;
import souther.compiler.semantics.CodePointClass;
import souther.compiler.types.Type;
import souther.compiler.values.Value;
import souther.compiler.values.ValueSet;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * The numbers terms come to of the values a position's rules name are read of those values, one
 * value at a time and every term of it together.
 *
 * <p>Two values coming to one number are one number, a set that is not finitely many values holds
 * the number to nothing, and terms of two positions are not read of one value.
 */
class WhatATermComesToOfTheValuesNamedIsReadOfThoseValuesTest {

    private static final Symbols SYMBOLS = Symbols.none(DefaultStdlib.get());

    private static final Carrier TEXT = new Carrier.Text();

    private static TermOrders notWhitespaceOf(String position) {
        return TermOrdersFixtures.at(NumericTerm.CodePointClassCount.of(
                        TermPath.of(position), new CodePointClass.NotWhitespace(), Type.STRING,
                        ScopedDeclarations.wrapsOf(SYMBOLS)),
                Type.STRING, SYMBOLS);
    }

    @Test
    void eachValueIsReadThroughTheTerm() {
        TermOrders orders = notWhitespaceOf("c");
        ValueSet trimmedToOne = ValueSet.oneOf(Set.of(Value.text("a"), Value.text(" b ")));
        ValueSet trimmedToTwoOrOne = ValueSet.oneOf(Set.of(Value.text("ab"), Value.text("c")));

        assertEquals(ValueSet.oneOf(Set.of(Value.number(1))),
                ReadingsOfEachValue.of(trimmedToOne, List.of(orders)).comeTo(orders),
                "\"a\" and \" b \" each hold one code point that is not whitespace");
        assertEquals(ValueSet.oneOf(Set.of(Value.number(1), Value.number(2))),
                ReadingsOfEachValue.of(trimmedToTwoOrOne, List.of(orders)).comeTo(orders));
    }

    /**
     * Two terms of one position are read of each value together, so what comes back is which value
     * comes to which pair, and not a pair out of each term's numbers put together.
     *
     * <p>{@code " a"} and {@code "c"} are both one code point that is not whitespace, and the value
     * is what tells them apart: read apart, the value {@code " a"} and a count of two would be a pair
     * of the two sets, and no value is both.
     */
    @Test
    void everyTermIsReadOfOneValueAtOnce() {
        TermOrders count = notWhitespaceOf("c");
        TermOrders itself = TermOrdersFixtures.itself(
                new NumericTerm.ValueOf(TermPath.of("c")), TEXT);
        ReadingsOfEachValue read = ReadingsOfEachValue.of(ValueSet.oneOf(
                        Set.of(Value.text(" a"), Value.text("bb"), Value.text("c"))),
                List.of(itself, count));

        Set<List<Value>> pairs = new HashSet<>();
        for (ReadingsOfEachValue.Read each : read.each()) {
            pairs.add(List.of(TEXT.valueAt(each.numbers().get(itself.term())),
                    count.answered().valueAt(each.numbers().get(count.term()))));
        }
        assertEquals(Set.of(List.of(Value.text(" a"), Value.number(1)),
                List.of(Value.text("bb"), Value.number(2)),
                List.of(Value.text("c"), Value.number(1))), pairs);
    }

    @Test
    void aSetThatIsNotFinitelyManyValuesHoldsTheNumberToNothing() {
        assertNull(ReadingsOfEachValue.of(ValueSet.allBut(Value.text("a")),
                List.of(notWhitespaceOf("c"))));
    }

    /**
     * A value no term can read leaves the values unread together, rather than read without it: a
     * reader holding the rest would take what that value comes to for something nothing comes to.
     */
    @Test
    void aValueATermCannotReadLeavesTheValuesUnread() {
        TermOrders whole = TermOrdersFixtures.itself(new NumericTerm.ValueOf(TermPath.of("c")),
                new Carrier.Whole());
        assertNotNull(ReadingsOfEachValue.of(ValueSet.oneOf(Set.of(Value.number(1))),
                List.of(whole)), "a whole number is read on the order of the whole numbers");
        assertNull(ReadingsOfEachValue.of(
                ValueSet.oneOf(Set.of(Value.number(1), Value.text("a"))), List.of(whole)),
                "and a string beside it is not");
    }

    @Test
    void termsOfTwoPositionsAreNotReadOfOneValue() {
        assertNull(ReadingsOfEachValue.of(ValueSet.oneOf(Set.of(Value.text("a"))),
                List.of(notWhitespaceOf("c"), notWhitespaceOf("d"))));
    }
}
