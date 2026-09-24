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
 * <p>A kernel's application settles what it takes each argument as, and the call holds each
 * argument at exactly that. {@code String.matches}'s pattern is a fact settled beside it: the
 * checker folds its first argument under the bindings in force and asks {@code
 * java.util.regex.Pattern} whether the composed text is accepted, which settles one string. Both
 * belong on the call they were settled for — not folded into {@code args}, which is what the body
 * evaluates at run time and a different question — and not left for a reader below to derive a
 * second time.
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

    private static final Core.Reached.OfKernel EMPTY_MAP = new Core.Reached.OfKernel(
            new ReachName.OfLibrary(ValueName.Stdlib.operation("Map", "empty")),
            Kernel.MAP_EMPTY);

    private static final Core.Reached.OfDeclaration HELPER = new Core.Reached.OfDeclaration(
            new ReachName.Own(new ValueName.Helper("demo", "half")));

    private static final List<Type> TWO_STRINGS = List.of(Type.STRING, Type.STRING);

    private static Core.Str str(String s) {
        return new Core.Str(s, Type.STRING, POS);
    }

    private static Core.CallSettlement.AtKernel at(List<Type> takes, Core.KernelFact fact) {
        return new Core.CallSettlement.AtKernel(takes, fact);
    }

    private static Core.CallSettlement.AtKernel matching(String pattern) {
        return at(TWO_STRINGS, new Core.KernelFact.StringMatches(pattern));
    }

    @Test
    void aStringMatchesCallCarriesWhatItTakesAndItsSettledPattern() {
        Core.Call call = new Core.Call(MATCHES, List.of(str("AB-[0-9]{4}"), str("AB-1234")),
                UNWRITTEN, matching("AB-[0-9]{4}"), Type.BOOL, POS);

        assertEquals(matching("AB-[0-9]{4}"), call.settlement());
    }

    /** A pattern is {@code String.matches}'s own fact, so a call reaching any other kernel is
     *  refused one. */
    @Test
    void aCallToAnyOtherKernelIsRefusedAPattern() {
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> new Core.Call(TRIM, List.of(str("  x  ")), UNWRITTEN,
                        at(List.of(Type.STRING), new Core.KernelFact.StringMatches("x")),
                        Type.STRING, POS));

        assertTrue(e.getMessage().contains("String.trim"), e.getMessage());
    }

    /** And a call that does reach {@code String.matches} is held to carrying one: the checker settles
     *  the pattern as part of typing the call, not as a step a later pass might skip. */
    @Test
    void aStringMatchesCallIsRefusedNoPattern() {
        assertThrows(IllegalArgumentException.class,
                () -> new Core.Call(MATCHES, List.of(str("x"), str("x")), UNWRITTEN,
                        at(TWO_STRINGS, Core.KernelFact.None.INSTANCE), Type.BOOL, POS));
    }

    /** A kernel's application always settles what it takes, so a call reaching a kernel with no
     *  settlement is one whose arguments nobody said the types of. */
    @Test
    void aKernelCallIsRefusedNoSettlement() {
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> new Core.Call(TRIM, List.of(str("  x  ")), UNWRITTEN,
                        Core.CallSettlement.None.INSTANCE, Type.STRING, POS));

        assertTrue(e.getMessage().contains("String.trim"), e.getMessage());
    }

    /** A kernel taking no argument settles that it takes none, which is a settlement like any
     *  other. */
    @Test
    void aKernelTakingNothingSettlesThatItTakesNothing() {
        Core.Call call = new Core.Call(EMPTY_MAP, List.of(), UNWRITTEN,
                at(List.of(), Core.KernelFact.None.INSTANCE), new Type.MapOf(Type.STRING, Type.INT),
                POS);

        assertEquals(List.of(), ((Core.CallSettlement.AtKernel) call.settlement()).takes());
    }

    /** And a kernel taking nothing is refused no settlement, as any kernel call is. */
    @Test
    void aKernelTakingNothingIsRefusedNoSettlement() {
        assertThrows(IllegalArgumentException.class,
                () -> new Core.Call(EMPTY_MAP, List.of(), UNWRITTEN,
                        Core.CallSettlement.None.INSTANCE, new Type.MapOf(Type.STRING, Type.INT),
                        POS));
    }

    /** A call to a declaration takes its arguments as the declaration says, so it is refused a
     *  kernel's settlement — the way a rewrite that turned a kernel call into something else while
     *  leaving the settlement behind would be. */
    @Test
    void aCallToADeclarationIsRefusedAKernelsSettlement() {
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> new Core.Call(HELPER, List.of(str("x")), UNWRITTEN,
                        at(List.of(Type.STRING), Core.KernelFact.None.INSTANCE), Type.STRING, POS));

        assertTrue(e.getMessage().contains("half"), e.getMessage());
    }

    @Test
    void aKernelCallIsRefusedASettlementTakingAnotherNumberOfArguments() {
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> new Core.Call(TRIM, List.of(str("  x  ")), UNWRITTEN,
                        at(TWO_STRINGS, Core.KernelFact.None.INSTANCE), Type.STRING, POS));

        assertTrue(e.getMessage().contains("String.trim"), e.getMessage());
    }

    /** An argument of another type than the application takes it as is refused, and a narrower one
     *  is no exception: where it may stand as the wider type, a {@link Core.Widen} says so. */
    @Test
    void aKernelCallIsRefusedAnArgumentOfAnotherTypeThanItTakes() {
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> new Core.Call(TRIM, List.of(new Core.Int(1, Type.INT, POS)), UNWRITTEN,
                        at(List.of(Type.STRING), Core.KernelFact.None.INSTANCE), Type.STRING, POS));

        assertTrue(e.getMessage().contains("argument 1"), e.getMessage());
    }

    /**
     * A rewrite that replaces an argument still applies the same kernel, so the settlement the
     * checker proved about that application is not this pass's to drop — the same rule that already
     * holds for what a call applies and which occurrence it is.
     */
    @Test
    void aRewriteOfACallsArgumentsKeepsItsSettlement() {
        Core.Call call = new Core.Call(MATCHES, List.of(str("AB-[0-9]{4}"), str("AB-1234")),
                UNWRITTEN, matching("AB-[0-9]{4}"), Type.BOOL, POS);

        Core rewritten = Core.mapChildren(call,
                child -> child == call.args().get(1) ? str("AB-9999") : child,
                name -> name, construct -> construct);

        assertEquals(call.settlement(), ((Core.Call) rewritten).settlement());
        assertEquals(List.of(str("AB-[0-9]{4}"), str("AB-9999")), ((Core.Call) rewritten).args());
    }

    /** And keeps it rather than settling it again: a rewrite that hands an argument of another type
     *  is refused, not followed. */
    @Test
    void aRewriteThatChangesAnArgumentsTypeIsRefused() {
        Core.Call call = new Core.Call(MATCHES, List.of(str("AB-[0-9]{4}"), str("AB-1234")),
                UNWRITTEN, matching("AB-[0-9]{4}"), Type.BOOL, POS);

        assertThrows(IllegalArgumentException.class, () -> Core.mapChildren(call,
                child -> child == call.args().get(1) ? new Core.Int(1, Type.INT, POS) : child,
                name -> name, construct -> construct));
    }

    /** A no-op rewrite still keeps the node it walked, settlement included. */
    @Test
    void aWalkThatChangesNothingKeepsTheCallItWalked() {
        Core.Call call = new Core.Call(MATCHES, List.of(str("AB-[0-9]{4}"), str("AB-1234")),
                UNWRITTEN, matching("AB-[0-9]{4}"), Type.BOOL, POS);

        assertSame(call, Core.mapChildren(call, c -> c, n -> n, b -> b));
    }

    /** {@code TRIM} carries no ordering constraint of its own, but the invariant does not hold a
     *  second table of which kernels may — that is CallElaborator's decision. It asks only that the
     *  kernel is not {@code String.matches}, which has its own fact and no other. */
    @Test
    void anOrderingSubjectIsAcceptedOnAKernelCallOtherThanStringMatches() {
        Core.Call call = new Core.Call(TRIM, List.of(str("  x  ")), UNWRITTEN,
                at(List.of(Type.STRING), new Core.KernelFact.OrderingSubject(Type.INT)),
                Type.STRING, POS);

        assertEquals(new Core.KernelFact.OrderingSubject(Type.INT),
                ((Core.CallSettlement.AtKernel) call.settlement()).fact());
    }

    /** {@code String.matches} carries its own fact and no other — the same exclusivity
     *  {@code aStringMatchesCallIsRefusedNoPattern} states from the other side, which an
     *  {@code OrderingSubject} must not quietly open a way around. */
    @Test
    void aStringMatchesCallIsRefusedAnOrderingSubject() {
        assertThrows(IllegalArgumentException.class,
                () -> new Core.Call(MATCHES, List.of(str("x"), str("x")), UNWRITTEN,
                        at(TWO_STRINGS, new Core.KernelFact.OrderingSubject(Type.INT)),
                        Type.BOOL, POS));
    }
}
