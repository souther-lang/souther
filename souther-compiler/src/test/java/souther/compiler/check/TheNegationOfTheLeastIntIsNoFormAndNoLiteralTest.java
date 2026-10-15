package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.frontend.CstFrontend;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Place;
import souther.compiler.types.Type;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * The checked form reads the negation of the smallest {@code Int} as the run time does: no number.
 *
 * <p>{@code --9223372036854775808} is one negation over the one literal the smallest {@code Int} is
 * written as, and the run time aborts on it. A literal reader that negated the count, and an affine
 * reader that negated the form of its operand, would each put {@code +2^63} where no run has a
 * value — a line drawn for a comparison against a bound nobody can reach.
 */
class TheNegationOfTheLeastIntIsNoFormAndNoLiteralTest {

    private static final SourcePos SOMEWHERE = new SourcePos(1, 1);

    private static final Symbols SYMBOLS = symbols();

    private static Core.Int number(long value) {
        return new Core.Int(value, Type.INT, SOMEWHERE);
    }

    private static Core negated(Core operand) {
        return new Core.Neg(operand, Type.INT, SOMEWHERE);
    }

    @Test
    void theLeastIntIsALiteral() {
        assertEquals(Count.of(Long.MIN_VALUE), literalOf(number(Long.MIN_VALUE)));
    }

    @Test
    void itsNegationIsNoLiteral() {
        assertNull(literalOf(negated(number(Long.MIN_VALUE))));
    }

    @Test
    void anyOtherNegationIsALiteral() {
        assertEquals(Count.of(-5L), literalOf(negated(number(5))));
        assertEquals(Count.of(Long.MAX_VALUE), literalOf(negated(number(Long.MIN_VALUE + 1))));
    }

    /** What the carrier of a whole number reads {@code e} as, where no name stands for anything. */
    private static Place literalOf(Core e) {
        return Carrier.WHOLE.literalOf(new ValueStanding.Standing<>(e, "nowhere", reading()),
                SYMBOLS);
    }

    @Test
    void itsNegationIsNoForm() {
        assertNull(AffineForms.of(negated(number(Long.MIN_VALUE)), "nowhere", reading()));
        assertNull(AffineForms.of(negated(negated(number(Long.MIN_VALUE))), "nowhere", reading()));
    }

    @Test
    void theLeastIntItselfAndAnyOtherNegationAreForms() {
        LinearForm<String> least = AffineForms.of(number(Long.MIN_VALUE), "nowhere", reading());
        assertNotNull(least);
        assertEquals(ExactRatio.of(Long.MIN_VALUE), least.constant());

        LinearForm<String> five = AffineForms.of(negated(number(5)), "nowhere", reading());
        assertNotNull(five);
        assertEquals(ExactRatio.of(-5), five.constant());
    }

    /** A reading with no name in it: nothing here stands for a position, so a form is a constant
     *  the grammar composed or none. */
    private static AffineForms.Reading<String, String> reading() {
        return new AffineForms.Reading<>() {

            @Override
            public Symbols symbols() {
                return SYMBOLS;
            }

            @Override
            public DeclarationAccess declarations() {
                return DeclarationAccess.NONE;
            }

            @Override
            public LinearForm<String> leafOf(Core e, String at) {
                return null;
            }

            @Override
            public String inside(Core.LetIn li, String at) {
                return at;
            }

            @Override
            public ValueStanding.ReadThrough<String> readThrough(Core.Read read, String at) {
                return null;
            }

            @Override
            public List<ValueStanding.ReadThrough<String>> alternativesOf(Core.Read read, String at) {
                return null;
            }

            @Override
            public boolean readsThrough(Core.FieldAccess fa, String at) {
                return false;
            }
        };
    }

    private static Symbols symbols() {
        Ast.Module parsed = CstFrontend.parse("module demo\n");
        Hir.Module resolved = Resolve.module(parsed, SyntaxSymbols.of(parsed, DefaultStdlib.get()));
        return Symbols.of(resolved, DefaultStdlib.get());
    }
}
