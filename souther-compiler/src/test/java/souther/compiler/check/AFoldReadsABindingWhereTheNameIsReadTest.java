package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Hir;
import souther.compiler.ast.WrittenName;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a fold makes of an expression that binds a name.
 *
 * <p>A {@code let} is part of the expression rather than a name to look up, and almost every one a
 * fold meets is a binding no author typed: a helper call is expanded as a binding over the helper's
 * body, and a value read as a shared materialisation is one too. A fold that stopped at a binding
 * would answer that the same program is constant written one way and not the other.
 *
 * <p>Read where the name is read, which is the environment's rule and not this reader's (ADR-0106,
 * ADR-0111). So a binding the body never reads is never folded, and what it was given not being
 * constant says nothing about the body that ignores it. What is asked here is whether the answer is
 * known at compile time; whether the whole expression could be run at compile time is a different
 * question, and nothing here asks it.
 */
class AFoldReadsABindingWhereTheNameIsReadTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static final BindingOwner OWNER = new BindingOwner.OfValue("m", "v");

    private static Hir.Binder binder(String name, int ordinal) {
        return new Hir.Binder(WrittenName.synthetic(name, POS), new BindingId(OWNER, ordinal), POS);
    }

    private static Hir.Expr read(Hir.Binder binder) {
        return Hir.Var.local(binder, POS);
    }

    private static Hir.Expr let(Hir.Binder binder, Hir.Expr value, Hir.Expr body) {
        return new Hir.LetIn(binder, value, null, false, null, body, POS, null);
    }

    private static Hir.Expr binary(BinOp op, Hir.Expr left, Hir.Expr right) {
        return new Hir.Binary(op, left, right,
                SourceConstructOrigin.written(new WrittenOwner.Body("m", "b"), 0,
                        SourceConstruct.BINARY),
                POS, null);
    }

    private static Optional<Object> fold(Hir.Expr e) {
        return ConstEval.against(Symbols.none(DefaultStdlib.get())).eval(e);
    }

    /** A binding holding a written string is the string wherever the name is read. */
    @Test
    void aNameStandsForWhatItWasGiven() {
        Hir.Binder x = binder("x", 0);
        assertEquals(Optional.of("ab"),
                fold(let(x, new Hir.StringLit("a", POS, null),
                        binary(BinOp.CONCAT, read(x), new Hir.StringLit("b", POS, null)))));
    }

    /**
     * And through a second binding written over the first, read twice.
     *
     * <p>Two bindings rather than one because a chain is what a body of any size is: each binding
     * reads the ones before it, and a fold that could follow one step but not two would answer a
     * program by how many names its author gave the parts.
     */
    @Test
    void aChainOfBindingsIsFollowedToTheEnd() {
        Hir.Binder x = binder("x", 0);
        Hir.Binder y = binder("y", 1);
        assertEquals(Optional.of(4L),
                fold(let(x, new Hir.IntLit(1, POS, null),
                        let(y, binary(BinOp.ADD, read(x), new Hir.IntLit(1, POS, null)),
                                binary(BinOp.MUL, read(y), read(y))))));
    }

    /**
     * A binding the body never reads is never folded, so what it holds cannot make the body
     * unknown.
     *
     * <p>This is the demand the environment states: a value stands for the name where the name is
     * read. Folded on the way in instead, an expression would stop being constant for a binding
     * written beside it that nothing uses.
     */
    @Test
    void aBindingNothingReadsIsNotFolded() {
        Hir.Binder x = binder("x", 0);
        // A field read of a name nothing here declares: outside the fragment a fold reaches, which
        // is what makes it the value this test needs.
        assertEquals(Optional.of("a"),
                fold(let(x, unfoldable(), new Hir.StringLit("a", POS, null))));
    }

    /** And a name whose binding does not fold is not a constant, which is the other half of the
     *  one above: the binding is read, and reading it is what says there is no answer. */
    @Test
    void aNameGivenSomethingUnfoldableIsNotAConstant() {
        Hir.Binder x = binder("x", 0);
        assertEquals(Optional.empty(), fold(let(x, unfoldable(), read(x))));
    }

    /** A field read of a name nothing here declares: outside the fragment a fold reaches, which is
     *  what makes it the value these two need. */
    private static Hir.Expr unfoldable() {
        return new Hir.FieldAccess(
                new Hir.Var.Unanswered(WrittenName.synthetic("t", POS), null, null),
                WrittenName.synthetic("value", POS), POS, null);
    }
}
