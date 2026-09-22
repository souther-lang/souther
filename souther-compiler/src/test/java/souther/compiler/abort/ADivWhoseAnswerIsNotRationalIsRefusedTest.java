package souther.compiler.abort;

import souther.compiler.DefaultStdlib;
import souther.compiler.core.Core;
import souther.compiler.core.KernelContracts;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BinOp;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.Type;
import souther.compiler.types.WrittenOwner;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@code /} always answers {@code Rational} (spec §stdlib-rational, ADR-0116) — never {@code Int}
 * or {@code Decimal}, the way {@code +}, {@code -} and {@code *} can. The checker never writes a
 * {@code Core.Binary(DIV, ...)} of any other answer type, and {@code BodyGen} itself has no kernel
 * to lower one to; a {@code Core} claiming otherwise is built by hand here, because what is tested
 * is that {@link AbortSites} refuses it rather than silently answering the site as though it were
 * an ordinary {@code Int} division.
 */
class ADivWhoseAnswerIsNotRationalIsRefusedTest {

    private static final SourcePos POS = new SourcePos(1, 1);
    private static final KernelContracts KERNELS =
            KernelContracts.of(DefaultStdlib.get().kernelSignatures());

    @Test
    void aDivWhoseAnswerIsIntIsRefused() {
        SourceConstructOrigin origin = SourceConstructOrigin.written(
                new WrittenOwner.Body("demo", "go"), 0, SourceConstruct.IF);
        Core.Binary malformed = new Core.Binary(BinOp.DIV,
                new Core.Int(4, Type.INT, POS), new Core.Int(2, Type.INT, POS),
                ConstructOccurrence.asWritten(origin), Type.INT, POS);

        IllegalStateException thrown = assertThrows(IllegalStateException.class,
                () -> AbortSites.of(List.of(malformed), KERNELS, Set.of()));

        assertTrue(thrown.getMessage().contains("Rational"), thrown.getMessage());
    }
}
