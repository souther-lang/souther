package souther.compiler.abort;

import souther.compiler.DefaultStdlib;
import souther.compiler.core.Core;
import souther.compiler.core.Kernel;
import souther.compiler.core.KernelContracts;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BinOp;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.ReachName;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.ValueName;
import souther.compiler.types.WrittenOwner;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A site one of whose own children never answers a value is never reached itself, so it does not
 * carry whatever it would otherwise be classified for — {@link AbortSites#aChildNeverAnswers}.
 *
 * <p>Built by hand. An extensive search for a source program the checker both accepts and types
 * with a {@code Type.Never} operand at {@code +}, {@code /}, a construction's field, or a kernel
 * call's argument did not turn one up: every combination tried either failed E1307 (the checker
 * would not give {@code unreachable} a type in that position at all) or, once a position did accept
 * one, failed E1326 (nothing ruled the reached case out, so {@code unreachable} was itself refused).
 * Whether some other combination of context and invariant threads both needles is not settled here.
 * What is tested is that {@link AbortSites} answers correctly <em>if</em> the checker ever hands it
 * such a {@code Core} — today, or after some future change to what {@code unreachable} may stand
 * beside — rather than crashing on a shape that looks malformed only because a child of it diverges.
 */
class ASiteWithANeverChildNeverAbortsOnItsOwnAccountTest {

    private static final SourcePos POS = new SourcePos(1, 1);
    private static final TypeSymbol.AtModule PERSON = TypeSymbols.declared(new TypeKey("demo", "Person"));
    private static final KernelContracts KERNELS =
            KernelContracts.of(DefaultStdlib.get().kernelSignatures());

    private static Core.Unreachable never() {
        return new Core.Unreachable("never", Type.NEVER, POS);
    }

    private static SourceConstructOrigin origin() {
        return SourceConstructOrigin.written(new WrittenOwner.Body("demo", "go"), 0,
                SourceConstruct.IF);
    }

    /** {@code a + unreachable "never"}: the checker would defer this to {@code Int} (the left
     *  side's type), never to {@code Rational} the way an ordinary {@code Int + Int} answering
     *  {@code Rational} could not — the exact shape that would otherwise reach
     *  {@link AbortSites}'s "no arithmetic the checker admits answers with" refusal. */
    @Test
    void anAddWithANeverOperandAbortsOnNeitherAccount() {
        Core.Binary add = new Core.Binary(BinOp.ADD, new Core.Int(1, Type.INT, POS), never(),
                ConstructOccurrence.asWritten(origin()), Type.INT, POS);

        AbortSites sites = AbortSites.of(List.of(add), KERNELS, Set.of());

        assertTrue(sites.at(add).isEmpty(), "the + is never reached, whatever it would answer for");
    }

    /** {@code a / unreachable "never"}: the shape {@link AbortSites#divide}'s
     *  {@code binary.type() != Type.RATIONAL} invariant check exists to refuse as malformed — except
     *  this one is not malformed, the operator is simply never reached. */
    @Test
    void aDivWithANeverOperandAbortsOnNeitherAccount() {
        Core.Binary div = new Core.Binary(BinOp.DIV, new Core.Int(1, Type.INT, POS), never(),
                ConstructOccurrence.asWritten(origin()), Type.INT, POS);

        AbortSites sites = AbortSites.of(List.of(div), KERNELS, Set.of());

        assertTrue(sites.at(div).isEmpty(), "the / is never reached, whatever type it carries");
    }

    /** A construction one of whose fields never answers is never attempted, so it does not carry
     *  {@link AbortKind#INVARIANT_NOT_HELD} even where the type it would have built has a clause. */
    @Test
    void aConstructionWithANeverFieldNeverChecksTheInvariantItWouldHave() {
        Core.Construct construct = new Core.Construct(PERSON,
                List.of(new Core.FieldValue("age", never(), POS)), Type.ref(PERSON), POS);

        AbortSites sites = AbortSites.of(List.of(construct), KERNELS, Set.of(PERSON));

        assertTrue(sites.at(construct).isEmpty(), "the construction is never attempted");
    }

    /** A kernel call one of whose arguments never answers is never reached either, so it does not
     *  carry what the kernel it would have called can otherwise end without a value for. */
    @Test
    void aKernelCallWithANeverArgumentNeverRunsTheKernel() {
        Core.Call call = new Core.Call(
                new Core.Reached.OfKernel(
                        new ReachName.OfLibrary(new ValueName.Stdlib.Operation("Int", "floorMod")),
                        Kernel.INT_FLOOR_MOD),
                List.of(new Core.Int(1, Type.INT, POS), never()),
                ConstructOccurrence.asWritten(origin()), Core.CallSettlement.None.INSTANCE,
                Type.INT, POS);

        AbortSites sites = AbortSites.of(List.of(call), KERNELS, Set.of());

        assertTrue(sites.at(call).isEmpty(), "the call is never reached");
    }
}
