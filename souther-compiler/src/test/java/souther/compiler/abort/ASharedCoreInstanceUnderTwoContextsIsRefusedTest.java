package souther.compiler.abort;

import souther.compiler.DefaultStdlib;
import souther.compiler.core.Core;
import souther.compiler.core.KernelContracts;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.WrittenOwner;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@code Core} does not refuse a node from standing in two places at once, and nothing in
 * {@link AbortSites} may assume a body stays a tree rather than a future rewrite sharing a node
 * across it. Built by hand — {@code Core} nodes this compiler emits never alias today — because
 * what is tested here is the safety net for the day one does, not today's shape.
 */
class ASharedCoreInstanceUnderTwoContextsIsRefusedTest {

    private static final SourcePos POS = new SourcePos(1, 1);
    private static final BindingOwner OWNER = new BindingOwner.OfValue("demo", "go");
    private static final TypeSymbol.AtModule PERSON = TypeSymbols.declared(new TypeKey("demo", "Person"));
    private static final KernelContracts KERNELS =
            KernelContracts.of(DefaultStdlib.get().kernelSignatures());

    private static Core.Construct construction() {
        return new Core.Construct(PERSON, List.of(new Core.FieldValue("age",
                new Core.Int(1, Type.INT, POS), POS)), Type.ref(PERSON), POS);
    }

    private static Core.Binder binder(String name) {
        return new Core.Binder(name, new BindingId(OWNER, 0));
    }

    /**
     * The one {@code Core.Construct} instance stands twice: once as an ordinary element of a
     * {@code Tuple} — where an unheld invariant aborts — and once as the construction an
     * {@code IfConstructed} beside it tests — where the same failure branches instead. One
     * instance, two contexts, two disagreeing answers.
     */
    @Test
    void oneSharedConstructUnderTwoContextsIsRefused() {
        Core.Construct shared = construction();
        SourceConstructOrigin origin = SourceConstructOrigin.written(
                new WrittenOwner.Body("demo", "go"), 0, SourceConstruct.IF);
        Core.IfConstructed attempt = new Core.IfConstructed(shared, binder("p"),
                new Core.Int(0, Type.INT, POS),
                List.of(new Core.ElseArm(Optional.empty(), new Core.Int(1, Type.INT, POS))),
                Core.ForkPlace.asWritten(ConstructOccurrence.asWritten(origin)), Type.INT, POS);
        Core root = new Core.Tuple(List.of(shared, attempt), Type.INT, POS);

        IllegalStateException thrown = assertThrows(IllegalStateException.class,
                () -> AbortSites.of(List.of(root), KERNELS, Set.of(PERSON)));

        assertTrue(thrown.getMessage().contains("INVARIANT_NOT_HELD"), thrown.getMessage());
    }
}
