package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What a map holds is a position of the input, and one the rules of the input can name.
 *
 * <p>Asked here, where the reading of an input is made, and not of whatever goes on to ask about a
 * number there. A body handed a map's values compares them as numbers of this input, and every
 * reader after this one names such a number through a value whose rules reach it — so a map the
 * walk did not go into leaves a term at its values that no reader further on can name, and what
 * fails then is that reader, far from the cause.
 */
class WhatAMapHoldsIsAPositionOfTheInputTest {

    /** A map of numbers beside a field, and nothing the record says about either. */
    private static final String A_MAP_BESIDE_A_FIELD = """
            module example.beside

            data Usage = { counts: Map<String, Int>, atLeast: Int }

            data Taken

            behavior take : (u: Usage) -> Taken
            """;

    private static final TermPath VALUES = TermPath.of("u").then("counts").element();

    /** The walk goes into the map, and what stands at the element is what the map holds. */
    @Test
    void theValuesAreAPositionTheWalkReached() {
        Position values = read().inputs().at(VALUES);
        assertNotNull(values, "the walk read a position at the map's values");
        assertEquals(Type.INT, values.type(), "and it is what the map holds, not its key");
    }

    /** And a number there is one this input's rules can name, so it is asked about like any. */
    @Test
    void aNumberThereIsAskedAboutLikeAnyOther() {
        Read read = read();
        assertNotNull(read.inputs().quantities(read.rules())
                        .ordersOf(new NumericTerm.ValueOf(VALUES)).answered(),
                "an Int a map holds is measured on the order every Int is");
    }

    private record Read(InputDomain inputs, RuleReadingSource rules) {}

    private static Read read() {
        Compilation compilation = Compilation.ofSource(A_MAP_BESIDE_A_FIELD, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        return new Read(InputDomain.of(sigs.get("take"),
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES)), rules);
    }
}
