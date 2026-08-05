package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.ConstructionOrigin;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The operations the discharge representation keeps are the language's own, and each types from the
 * signature the library declared it with — variables and all, settled by the arguments it was given.
 * Nothing about the operation is written here: what is kept comes from the library, so one it gains
 * is kept without this being told.
 */
class ALanguageOperationKeptStandingTypesFromWhatItDeclaresTest {

    private static final SourcePos POS = new SourcePos(1, 1);
    private static final Preserved KEPT = Preserved.byTheLanguagesOwnOperations();

    @Test
    void aPolymorphicOperationSettlesItsVariablesFromItsArguments() {
        // List.length : (List<'a>) -> Int — the argument decides 'a, and the result is not a variable
        Ast.Expr call = new Ast.Apply("List.length", new ValueName.Stdlib("List.length"),
                List.of(new Ast.ListLit(List.of(new Ast.IntLit(1, POS)), POS)),
                ConstructionOrigin.own(), POS);

        Core typed = Elaborator.elaborate(call, Scope.NONE,
                CheckContext.of(Symbols.none()).preserving(KEPT));

        Core.PreservedCall kept = assertInstanceOf(Core.PreservedCall.class, typed);
        assertEquals(new ValueName.Stdlib("List.length"), kept.operation());
        assertEquals(Type.INT, kept.type());
    }

    @Test
    void theOperationsKeptAreTheLibrarysAndNotAListWrittenHere() {
        assertNotNull(KEPT.signatureOf(new ValueName.Stdlib("List.map")),
                "an operation the discharge rules are written about");
        assertNotNull(KEPT.signatureOf(new ValueName.Stdlib("String.length")),
                "and one they are not — what is kept is not decided by having a rule");
    }

    @Test
    void anOperationRewrittenAwayBeforeAnyOfThisIsNotKept() {
        // `List.fold` becomes `List.foldFrom` before this tree exists, so it has no declaration to
        // keep — and a rule keyed by it could never be looked up either
        assertTrue(KEPT.signatureOf(new ValueName.Stdlib("List.fold")) == null,
                "sugar has no declaration of its own");
        assertNotNull(KEPT.signatureOf(new ValueName.Stdlib("List.foldFrom")),
                "what it becomes does");
    }

    @Test
    void aModulesOwnHelperIsNotKeptByThisPolicy() {
        // nothing could be derived from leaving it standing, so it is expanded — and a tree that
        // still holds one is this compiler having failed to do that
        Ast.Expr call = new Ast.Apply("half", new ValueName.Helper("demo", "half"),
                List.of(new Ast.IntLit(1, POS)), ConstructionOrigin.own(), POS);

        assertThrows(RuntimeException.class, () -> Elaborator.elaborate(call, Scope.NONE,
                CheckContext.of(Symbols.none()).preserving(KEPT)));
    }
}
