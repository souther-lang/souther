package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.check.NewtypeInners;
import souther.compiler.check.ScopedDeclarations;
import souther.compiler.check.Symbols;
import souther.compiler.semantics.TakenArguments;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A number moved to another position is the same number taken there, and that includes what the
 * taking was given beside the value.
 *
 * <p>A quotient is the place divided by its divisor, so the divisor is part of which number it is: a
 * taking given none is no quotient at all. Moved without it, a number a line was drawn on at a sum
 * would be nothing under the case the row writes it at.
 */
class ANumberMovedIsTakenWithWhatItWasGivenTest {

    private static final Symbols SYMBOLS = Symbols.none(DefaultStdlib.get());

    private static final NewtypeInners INNERS = ScopedDeclarations.wrapsOf(SYMBOLS);

    private static final ValueName.Stdlib QUOTIENT =
            ValueName.Stdlib.operation("Int", "truncatingDivide");

    private static final TakenArguments BY_SEVEN = TakenArguments.at(1, BigDecimal.valueOf(7));

    @Test
    void aQuotientMovedKeepsItsDivisor() {
        NumericTerm.TakenOf atR = NumericTerm.TakenOf.of(QUOTIENT, TermPath.of("r"), BY_SEVEN,
                Type.INT, INNERS, SYMBOLS);
        assertNotNull(atR, "a quotient by seven is a number of the place");

        assertEquals(
                NumericTerm.TakenOf.of(QUOTIENT, TermPath.of("s"), BY_SEVEN, Type.INT, INNERS,
                        SYMBOLS),
                atR.movedTo(TermPath.of("s"), Type.INT, INNERS, SYMBOLS));
    }
}
