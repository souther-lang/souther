package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.ConstructionOrigin;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Typing is defined over what a representation is allowed to hold. The tree the backend emits from
 * has every call it cannot emit already expanded, so one arriving at call elaboration there is this
 * compiler having failed to expand it — not a program to type. That guard is what stops an expansion
 * bug from being emitted as something else, and it is fixed here before any representation is given
 * permission to keep a call standing.
 */
class AnUnexpandedCallIsOnlyTypedWhereARepresentationKeepsItTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    @Test
    void aStandardLibraryCallLeftStandingIsNotSomethingToType() {
        Ast.Expr call = new Ast.Apply("List.map", new ValueName.Stdlib("List", "map"),
                List.of(new Ast.IntLit(1, POS)), ConstructionOrigin.own(), POS);

        assertThrows(RuntimeException.class, () -> Elaborator.elaborate(call, Scope.NONE,
                CheckContext.of(Symbols.none())));
    }

    @Test
    void aHelperLeftStandingIsNotSomethingToTypeEither() {
        // a module's own `let` is expanded into the body that called it, so this is the same failure
        // as above and not a different one — the guard is about the representation, not about which
        // namespace the name was in
        Ast.Expr call = new Ast.Apply("half", new ValueName.Helper("demo", "half"),
                List.of(new Ast.IntLit(1, POS)), ConstructionOrigin.own(), POS);

        assertThrows(RuntimeException.class, () -> Elaborator.elaborate(call, Scope.NONE,
                CheckContext.of(Symbols.none())));
    }
}
