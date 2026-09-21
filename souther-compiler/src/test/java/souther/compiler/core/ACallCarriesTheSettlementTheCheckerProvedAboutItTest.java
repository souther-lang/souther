package souther.compiler.core;

import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.ReachName;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;
import souther.compiler.diag.SourcePos;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A call carries what the checker settled about it beside what it applies and what it evaluates.
 *
 * <p>{@code String.matches}'s pattern is the case in point: the checker folds its first argument
 * under the bindings in force and asks {@code java.util.regex.Pattern} whether the composed text is
 * accepted, which settles one string. That fact belongs on the call it was settled for — not folded
 * into {@code args}, which is what the body evaluates at run time and a different question — and not
 * left for a reader below to derive a second time from a shape it happens to recognise.
 */
class ACallCarriesTheSettlementTheCheckerProvedAboutItTest {

    private static final SourcePos POS = new SourcePos(1, 1);
    private static final ConstructOccurrence UNWRITTEN = ConstructOccurrence.unwritten();

    private static final Core.Reached.OfKernel MATCHES = new Core.Reached.OfKernel(
            new ReachName.OfLibrary(ValueName.Stdlib.operation("String", "matches")),
            Kernel.STRING_MATCHES);

    private static final Core.Reached.OfKernel TRIM = new Core.Reached.OfKernel(
            new ReachName.OfLibrary(ValueName.Stdlib.operation("String", "trim")),
            Kernel.STRING_TRIM);

    private static Core.Str str(String s) {
        return new Core.Str(s, Type.STRING, POS);
    }

    @Test
    void aStringMatchesCallCarriesItsSettledPattern() {
        Core.Call call = new Core.Call(MATCHES, List.of(str("AB-[0-9]{4}"), str("AB-1234")),
                UNWRITTEN, new Core.CallSettlement.StringMatches("AB-[0-9]{4}"), Type.BOOL, POS);

        assertEquals(new Core.CallSettlement.StringMatches("AB-[0-9]{4}"), call.settlement());
    }

    /** A settlement is {@code String.matches}'s own fact, so a call reaching any other kernel is
     *  refused one. */
    @Test
    void aCallToAnyOtherKernelIsRefusedAStringMatchesSettlement() {
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> new Core.Call(TRIM, List.of(str("  x  ")), UNWRITTEN,
                        new Core.CallSettlement.StringMatches("x"), Type.STRING, POS));

        assertTrue(e.getMessage().contains("String.trim"), e.getMessage());
    }

    /** And a call that does reach {@code String.matches} is held to carrying one: the checker settles
     *  the pattern as part of typing the call, not as a step a later pass might skip. */
    @Test
    void aStringMatchesCallIsRefusedNoSettlement() {
        assertThrows(IllegalArgumentException.class,
                () -> new Core.Call(MATCHES, List.of(str("x"), str("x")), UNWRITTEN,
                        Core.CallSettlement.None.INSTANCE, Type.BOOL, POS));
    }

    /**
     * A rewrite that replaces an argument still applies the same kernel, so the settlement the
     * checker proved about that application is not this pass's to drop — the same rule that already
     * holds for what a call applies and which occurrence it is.
     */
    @Test
    void aRewriteOfACallsArgumentsKeepsItsSettlement() {
        Core.CallSettlement.StringMatches settlement =
                new Core.CallSettlement.StringMatches("AB-[0-9]{4}");
        Core.Call call = new Core.Call(MATCHES, List.of(str("AB-[0-9]{4}"), str("AB-1234")),
                UNWRITTEN, settlement, Type.BOOL, POS);

        Core rewritten = Core.mapChildren(call,
                child -> child == call.args().get(1) ? str("AB-9999") : child,
                name -> name, construct -> construct);

        assertEquals(call.settlement(), ((Core.Call) rewritten).settlement());
        assertEquals(List.of(str("AB-[0-9]{4}"), str("AB-9999")), ((Core.Call) rewritten).args());
    }

    /** A no-op rewrite still keeps the node it walked, settlement included. */
    @Test
    void aWalkThatChangesNothingKeepsTheCallItWalked() {
        Core.Call call = new Core.Call(MATCHES, List.of(str("AB-[0-9]{4}"), str("AB-1234")),
                UNWRITTEN, new Core.CallSettlement.StringMatches("AB-[0-9]{4}"), Type.BOOL, POS);

        assertSame(call, Core.mapChildren(call, c -> c, n -> n, b -> b));
    }
}
