package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.NumericLiterals;
import souther.compiler.diag.SourcePos;
import souther.compiler.numeric.Count;

import java.math.BigDecimal;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A fixture generated for an {@code Int} is read as the number its text spells, whichever reader
 * reads it.
 *
 * <p>The smallest {@code Int} has no magnitude an {@code Int} holds, so a generated fixture cannot
 * be a negation of one: {@code Math.abs} leaves it negative, and a reader that negates
 * mathematically reads a number outside {@code Int}. It is one literal, as the source reads it.
 */
class TheLeastIntIsOneValueToEveryoneWhoReadsAFixtureTest {

    private static final long[] EDGES =
            {Long.MIN_VALUE, Long.MIN_VALUE + 1, -1, 0, 1, Long.MAX_VALUE - 1, Long.MAX_VALUE};

    @Test
    void theLeastIntIsOneLiteral() {
        FixtureTemplate least = FixtureTemplate.integer(Long.MIN_VALUE);

        assertEquals("-9223372036854775808", least.text());
        assertEquals(Long.MIN_VALUE, assertInstanceOf(Hir.IntLit.class, least.value()).value());
    }

    @Test
    void everyReaderReadsTheNumberTheTextSpells() {
        for (long each : EDGES) {
            FixtureTemplate template = FixtureTemplate.integer(each);
            assertEquals(Count.of(each), Counts.writtenIn(template.value()), template.text());
            assertEquals(BigDecimal.valueOf(each), NumericLiterals.literalOf(template.value()),
                    template.text());
        }
    }

    /** What no reader may read a number out of: the negation the run time aborts on. */
    @Test
    void theNegationOfTheLeastIntNamesNoNumber() {
        Hir.Expr negated = new Hir.Neg(new Hir.IntLit(Long.MIN_VALUE, new SourcePos(0, 0), null),
                new SourcePos(0, 0), null);

        assertNull(Counts.writtenIn(negated));
        assertNull(NumericLiterals.literalOf(negated));
    }
}
