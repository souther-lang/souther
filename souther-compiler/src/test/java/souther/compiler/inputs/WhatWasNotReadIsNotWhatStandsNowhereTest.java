package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.CoverageOrigin;
import souther.compiler.types.Type;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * An expression this reading does not follow is told apart from one that stands nowhere.
 *
 * <p>Two absences with nothing in common but that no path came back. Arithmetic over a position is
 * a value the input holds nowhere, and a reader told so is being told what the model says. An
 * expression binding a name of its own is one this reading does not go under, and what the model
 * says through it is exactly what is not known — so the same silence would be this compiler's reach
 * printed as a fact about somebody's rule.
 *
 * <p>Held at the reading rather than at a report, because that is where the two are still apart.
 * Every reader downstream may have one answer for them and says so by asking for the position alone;
 * what none of them can do is take one for the other without that being written where it happens.
 */
class WhatWasNotReadIsNotWhatStandsNowhereTest {

    private static final SourcePos POS = new SourcePos(0, 0);
    private static final BindingOwner OWNER = new BindingOwner.OfValue("example", "f");
    private static final BindingId PARAMETER = new BindingId(OWNER, 0);
    private static final BindingId LOCAL = new BindingId(OWNER, 1);

    private static InputReads reads() {
        return new InputReads(Map.of(PARAMETER, TermPath.of("n")), Map.of(),
                ElementBindings.NONE, Map.of(), false);
    }

    private static Core.Read parameter() {
        return new Core.Read("n", PARAMETER, Type.INT, POS);
    }

    private static PathResolution readingOf(Core e) {
        return reads().pathOf(e, Symbols.none(DefaultStdlib.get()));
    }

    /** The parameter itself is where it is. */
    @Test
    void aParameterIsAtItsPosition() {
        assertEquals(new PathResolution.At(TermPath.of("n")), readingOf(parameter()));
    }

    /** Arithmetic over it stands at no position, which is what the model says. */
    @Test
    void arithmeticOverAPositionStandsAtNone() {
        Core sum = new Core.Binary(souther.compiler.types.BinOp.ADD, parameter(),
                new Core.Int(1, Type.INT, POS), CoverageOrigin.unwritten(), Type.INT, POS);

        assertEquals(new PathResolution.NotAPosition(), readingOf(sum));
    }

    /** And an expression binding a name of its own is one this did not read, which is not that. */
    @Test
    void anExpressionThatBindsANameOfItsOwnIsNotRead() {
        Core through = new Core.LetIn(new Core.Binder("x", LOCAL), parameter(),
                new Core.Read("x", LOCAL, Type.INT, POS), Type.INT, POS);

        assertEquals(new PathResolution.Unread(
                        PathResolution.Reason.A_NAME_BOUND_INSIDE_THE_EXPRESSION),
                readingOf(through));
        assertInstanceOf(PathResolution.Unread.class, readingOf(through),
                "and never the answer arithmetic gets");
    }
}
