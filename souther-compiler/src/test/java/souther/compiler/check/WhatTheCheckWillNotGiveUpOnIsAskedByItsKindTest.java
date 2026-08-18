package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.CoverageOrigin;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * The check gives up on what it cannot read and refuses what it cannot square with itself, and which
 * of the two a failure is, is asked of the failure.
 *
 * <p>The boundary used to name the failures it knew of. That list is a copy of the distinction the
 * types already carry, and its way of going wrong is silent: a check that gains a new way to
 * disagree with itself keeps reporting that disagreement as an ordinary limit — a behavior with no
 * findings, which is what a behavior whose invariants all discharge produces — and nothing fails
 * while it does. Every failure of that kind is refused here because of what it is.
 */
class WhatTheCheckWillNotGiveUpOnIsAskedByItsKindTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static BindingId binding(int index) {
        return new BindingId(new BindingOwner.OfValue("demo", "f"), index);
    }

    /** A shape the walk has no rule for: swallowed, and the run-time check stands. */
    @Test
    void aFailureThatIsMerelyALimitIsGivenUpOn() {
        List<InvariantChecker.GaveUp> watching = new ArrayList<>();
        InvariantChecker.GAVE_UP = watching;
        try {
            assertDoesNotThrow(() -> InvariantChecker.gaveUp("a test",
                    new IllegalStateException("a shape with no rule")));
        } finally {
            InvariantChecker.GAVE_UP = null;
        }

        assertEquals(1, watching.size(), "recorded rather than raised");
    }

    /** One name given two kinds of number, which says the naming and the typing disagree. */
    @Test
    void oneNameGivenTwoKindsOfNumberIsRefused() {
        assertThrows(Terms.OneTermTwoKinds.class, () -> InvariantChecker.gaveUp("a test",
                new Terms.OneTermTwoKinds("`n` is DISCRETE and DENSE")));
    }

    /**
     * One atom recorded as two pieces of arithmetic, which says the same thing about a value the
     * affine fragment cannot carry.
     *
     * <p>Reached by asking the boundary rather than by contriving a program: nothing a program can
     * write makes the check contradict itself, which is what makes the boundary the only place the
     * answer can be held to.
     */
    @Test
    void oneAtomRecordedAsTwoPiecesOfArithmeticIsRefused() {
        Terms terms = new Terms(Symbols.none());
        BindingId a = binding(0);
        BindingId b = binding(1);
        Denotations at = Denotations.none().location(a, AsPlaces.of(a)).location(b, AsPlaces.of(b));
        Core.Read left = new Core.Read("a", a, Type.INT, POS);
        Core.Read right = new Core.Read("b", b, Type.INT, POS);
        NumericDomain.LinearForm<FactSubject> product = terms.affineOf(
                new Core.Binary(Hir.BinOp.MUL, left, right, CoverageOrigin.unwritten(), Type.INT,
                        POS), at);
        FactSubject atom = product.coefs().keySet().iterator().next();

        assertThrows(Terms.OneTermTwoDerivations.class, () -> InvariantChecker.gaveUp("a test",
                new Terms.OneTermTwoDerivations("atom `" + atom.rendered() + "` two ways")));
    }

    /** An atom recorded as arithmetic over itself, which says the naming built a value out of
     * itself. */
    @Test
    void anAtomComputedFromItselfIsRefused() {
        Terms terms = new Terms(Symbols.none());
        BindingId a = binding(0);
        Denotations at = Denotations.none().location(a, AsPlaces.of(a));
        FactSubject atom = terms.atomOf(new Core.Read("a", a, Type.INT, POS), at);

        assertThrows(DerivedBounds.AnAtomComputedFromItself.class,
                () -> InvariantChecker.gaveUp("a test",
                        new DerivedBounds.AnAtomComputedFromItself(atom)));
    }
}
