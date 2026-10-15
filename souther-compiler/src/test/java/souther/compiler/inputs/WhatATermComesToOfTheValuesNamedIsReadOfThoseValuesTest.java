package souther.compiler.inputs;

import org.junit.jupiter.api.Test;
import souther.compiler.DefaultStdlib;
import souther.compiler.check.ScopedDeclarations;
import souther.compiler.check.Symbols;
import souther.compiler.semantics.CodePointClass;
import souther.compiler.types.Type;
import souther.compiler.values.Value;
import souther.compiler.values.ValueSet;

import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The numbers a term comes to of the values a position's rules name are read of those values, one
 * by one, through the term.
 *
 * <p>Two values coming to one number are one number, and a set that is not finitely many values
 * holds the number to nothing.
 */
class WhatATermComesToOfTheValuesNamedIsReadOfThoseValuesTest {

    private static final Symbols SYMBOLS = Symbols.none(DefaultStdlib.get());

    @Test
    void eachValueIsReadThroughTheTerm() {
        TermOrders orders = TermOrdersFixtures.at(NumericTerm.CodePointClassCount.of(
                        TermPath.of("c"), new CodePointClass.NotWhitespace(), Type.STRING,
                        ScopedDeclarations.wrapsOf(SYMBOLS)),
                Type.STRING, SYMBOLS);
        ValueSet trimmedToOne = ValueSet.oneOf(Set.of(Value.text("a"), Value.text(" b ")));
        ValueSet trimmedToTwoOrOne = ValueSet.oneOf(Set.of(Value.text("ab"), Value.text("c")));

        assertEquals(ValueSet.oneOf(Set.of(Value.number(1))), orders.readOfEach(trimmedToOne),
                "\"a\" and \" b \" each hold one code point that is not whitespace");
        assertEquals(ValueSet.oneOf(Set.of(Value.number(1), Value.number(2))),
                orders.readOfEach(trimmedToTwoOrOne));
    }

    @Test
    void aSetThatIsNotFinitelyManyValuesHoldsTheNumberToNothing() {
        TermOrders orders = TermOrdersFixtures.at(NumericTerm.CodePointClassCount.of(
                        TermPath.of("c"), new CodePointClass.NotWhitespace(), Type.STRING,
                        ScopedDeclarations.wrapsOf(SYMBOLS)),
                Type.STRING, SYMBOLS);
        assertEquals(ValueSet.ANY, orders.readOfEach(ValueSet.allBut(Value.text("a"))));
    }
}
