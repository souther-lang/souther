package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.ConstructionOrigin;
import souther.compiler.types.Type;
import souther.compiler.types.ReachName;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Which calls survive is decided where a representation is built, and the checker is told. It asks
 * only whether this call is one of them — not what the operation means, which belongs to whoever
 * reads the representation. So an operation kept with no rule about it types like any other and
 * states nothing, and typing a call never waits on someone having a rule for it.
 */
class WhatARepresentationKeepsIsTheRepresentationsToSayTest {

    private static final SourcePos POS = new SourcePos(1, 1);
    private static final ValueName.Stdlib MAP = new ValueName.Stdlib("List", "map");

    /** `(Int) -> Int`, standing for whatever the operation was declared as. */
    private static final Type.FnOf SIGNATURE = (Type.FnOf) Type.fn(List.of(Type.INT), Type.INT);

    @Test
    void aKeptCallIsTypedFromTheSignatureItWasDeclaredWith() {
        Core typed = elaborate(callTo(MAP), keeping(MAP, SIGNATURE));

        Core.PreservedCall kept = assertInstanceOf(Core.PreservedCall.class, typed);
        assertEquals(MAP, kept.operation(), "what the name resolved to, not how it was written");
        assertEquals(Type.INT, kept.type());
    }

    @Test
    void aRepresentationThatKeepsNothingStillRefusesIt() {
        assertThrows(RuntimeException.class, () -> elaborate(callTo(MAP), Preserved.NONE));
    }

    @Test
    void anOperationThisRepresentationNeverSaidItKeepsIsStillARefusal() {
        // keeping one operation is not keeping the namespace it is in: a call this representation
        // never claimed is this compiler having failed to expand it, whichever library it names
        Preserved keepsMapOnly = keeping(MAP, SIGNATURE);

        assertThrows(RuntimeException.class,
                () -> elaborate(callTo(new ValueName.Stdlib("List", "filter")), keepsMapOnly));
    }

    @Test
    void aKeptCallAppliedToTheWrongNumberOfArgumentsIsSaidAsThat() {
        Hir.Expr twoArgs = new Hir.Apply("List.map", MAP, new ReachName.OfLibrary(MAP),
                List.of(new Hir.IntLit(1, POS, null), new Hir.IntLit(2, POS, null)),
                ConstructionOrigin.own(), POS, null);

        assertThrows(RuntimeException.class, () -> elaborate(twoArgs, keeping(MAP, SIGNATURE)));
    }

    @Test
    void aTreeThatBelongsToAnotherRepresentationDoesNotInheritThePermission() {
        // a body reaching a declaration's invariant reaches another tree, built by another question.
        // What it keeps is its own to say at its own entry; being reached from here is not a
        // representation having said anything.
        CheckContext keeping = CheckContext.of(Symbols.none(souther.compiler.DefaultStdlib.get())).preserving(keeping(MAP, SIGNATURE));

        assertEquals(Preserved.NONE, keeping.inAnotherRepresentation().preserved());
        assertEquals(Preserved.NONE, keeping.inAnotherRepresentation().forData(null).preserved(),
                "and it stays left behind as that tree is walked");
    }

    @Test
    void whichDataIsBeingCheckedIsNotWhereARepresentationEnds() {
        // `forData` moves within one representation as well, so it must not quietly mean the
        // permission is gone
        CheckContext keeping = CheckContext.of(Symbols.none(souther.compiler.DefaultStdlib.get())).preserving(keeping(MAP, SIGNATURE));

        assertEquals(keeping.preserved(), keeping.forData(null).preserved());
    }

    private static Hir.Expr callTo(ValueName.Stdlib operation) {
        return new Hir.Apply(operation.qualified(), operation, new ReachName.OfLibrary(operation),
                List.of(new Hir.IntLit(1, POS, null)), ConstructionOrigin.own(), POS, null);
    }

    private static Preserved keeping(ValueName operation, Type.FnOf signature) {
        return new Preserved(Map.of(operation,
                new CompleteSignature(signature.params(), signature.result())));
    }

    private static Core elaborate(Hir.Expr e, Preserved kept) {
        return Elaborator.elaborate(e, Scope.NONE,
                CheckContext.of(Symbols.none(souther.compiler.DefaultStdlib.get())).preserving(kept));
    }
}
