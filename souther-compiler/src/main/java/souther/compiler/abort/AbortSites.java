package souther.compiler.abort;

import souther.compiler.core.Core;
import souther.compiler.core.KernelContracts;
import souther.compiler.types.BinOp;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.IdentityHashMap;
import java.util.List;
import java.util.Set;

/**
 * Every {@link Core} site of a program, classified by which {@link AbortKind} a run reaching it can
 * end without a value for.
 *
 * <p>Read by identity and not by structural equality: {@code Core} is a record, and two occurrences
 * that happen to be built the same way — {@code x + 1} written twice — are equal without being the
 * one site this classified. What this answers is a fact about the occurrence a checked body holds,
 * so a lookup that collapsed equal-but-distinct occurrences together would answer one of them for
 * both, and get it right only where the two happened to agree.
 *
 * <p>Built once, over every body a program holds, by whoever assembles the {@code CheckedProgram} —
 * never by a backend re-walking {@code Core} to ask the same question a second time, which is the
 * shape this whole issue exists to end. A site not among {@link #at} is refused rather than answered
 * with {@link AbortSet#NONE}: those are not the same fact, and confusing "nobody classified this" for
 * "this cannot abort" is the exact drift a hand-kept table cannot be told apart from a considered
 * answer.
 *
 * <p><b>Context-sensitive, not a per-node-kind table.</b> {@link Core.Construct} aborts on an
 * unheld invariant only where nothing catches the failure first: one written directly as
 * {@link Core.IfConstructed#construct} takes its else arm instead, and never reaches an abort at
 * all. So classifying a site asks what stands over it as well as what it is — the same reason a
 * reader of what a body's arms declare cannot arrive at cannot switch on one node's own kind
 * either, and reads the body's evaluation structure instead.
 */
public final class AbortSites {

    private final IdentityHashMap<Core, AbortSet> local;

    private AbortSites(IdentityHashMap<Core, AbortSet> local) {
        this.local = local;
    }

    /**
     * Every reason a run reaching {@code site} can end without a value for.
     *
     * @throws IllegalArgumentException where {@code site} is not one this classified — never
     *     answered as {@link AbortSet#NONE}, which would read as "considered and found total"
     *     rather than as "not part of what this was built over"
     */
    public AbortSet at(Core site) {
        AbortSet found = local.get(site);
        if (found == null) {
            throw new IllegalArgumentException(
                    "this site is not one a program's AbortSites classified: " + site);
        }
        return found;
    }

    /**
     * Classifies every site under every {@code Core} in {@code roots} — a program's behavior bodies
     * and helper bodies, in whatever order a caller holds them in; order carries no meaning here.
     *
     * @param constructedWithInvariants every declared type at least one {@code invariant} clause
     *     names, read off the program's own declarations rather than re-derived here — the same
     *     answer {@link souther.compiler.program.CheckedData.WithFields#invariants} gives, asked
     *     once for the whole program rather than once per construction site
     */
    public static AbortSites of(List<Core> roots, KernelContracts kernels,
                                Set<TypeSymbol.AtModule> constructedWithInvariants) {
        IdentityHashMap<Core, AbortSet> local = new IdentityHashMap<>();
        for (Core root : roots) {
            walk(root, kernels, constructedWithInvariants, local);
        }
        return new AbortSites(local);
    }

    /**
     * Files {@code node}'s own local answer and recurses into its children — every child at the
     * same site's own local reading, except {@link Core.IfConstructed#construct}, which
     * {@link #walkGuarded} answers for.
     *
     * <p>A node already filed is not walked into a second time; {@link #file} says whether this is
     * the first time.
     */
    private static void walk(Core node, KernelContracts kernels,
                             Set<TypeSymbol.AtModule> constructedWithInvariants,
                             IdentityHashMap<Core, AbortSet> into) {
        if (!file(node, localAbortOf(node, kernels, constructedWithInvariants), into)) {
            return;
        }
        if (node instanceof Core.IfConstructed ic) {
            walkGuarded(ic.construct(), kernels, constructedWithInvariants, into);
            walk(ic.then(), kernels, constructedWithInvariants, into);
            for (Core.ElseArm arm : ic.els()) {
                walk(arm.body(), kernels, constructedWithInvariants, into);
            }
            return;
        }
        Core.forEachChild(node, child -> walk(child, kernels, constructedWithInvariants, into));
    }

    /**
     * {@code construct} as the one construction slot an {@link Core.IfConstructed} tests: an unheld
     * invariant takes the else arm rather than aborting, so this site's own answer is
     * {@link AbortSet#NONE} whatever {@link #localAbortOf} would have said for the same node stood
     * anywhere else. Its own children — the field initializers — are not guarded by anything and
     * walk the ordinary way: an initializer that itself divides by zero still aborts on the way to
     * building the value the attempt goes on to test.
     */
    private static void walkGuarded(Core.Construct construct, KernelContracts kernels,
                                    Set<TypeSymbol.AtModule> constructedWithInvariants,
                                    IdentityHashMap<Core, AbortSet> into) {
        if (!file(construct, AbortSet.NONE, into)) {
            return;
        }
        Core.forEachChild(construct,
                child -> walk(child, kernels, constructedWithInvariants, into));
    }

    /**
     * Files {@code node}'s answer, and says whether this is the first time — a caller recurses into
     * a node's children exactly where this answers {@code true}.
     *
     * <p>One map access on the common path ({@link IdentityHashMap#putIfAbsent}), not a
     * {@code containsKey} ahead of a {@code put}. But a second filing of the same node is not
     * silently accepted merely because it is cheap to detect: {@code Core} is immutable and this
     * walker's own {@link Core.IfConstructed} handling proves a node's context changes what it
     * means, so nothing here may assume {@code Core} bodies stay trees rather than becoming graphs
     * a future rewrite shares nodes across. A second filing that disagrees with the first is refused
     * outright — silently keeping whichever answer got there first would let the order two callers
     * happen to walk in decide what a shared site's own answer is, which is not a fact about the
     * site at all.
     *
     * @throws IllegalStateException where {@code node} was already filed with a different answer
     */
    private static boolean file(Core node, AbortSet answer, IdentityHashMap<Core, AbortSet> into) {
        AbortSet already = into.putIfAbsent(node, answer);
        if (already == null) {
            return true;
        }
        if (!already.equals(answer)) {
            throw new IllegalStateException("one Core instance is classified " + already
                    + " under one context and " + answer + " under another: " + node);
        }
        return false;
    }

    /**
     * What {@code node} itself — independent of any child — can end a run without a value for.
     *
     * <p>Exhaustive over {@link Core}. A node kind added later stops the build here, the same way
     * {@link Core#mapChildren} and {@link Core#forEachChild} are stopped by {@code Core}'s own
     * exhaustive switch.
     */
    private static AbortSet localAbortOf(Core node, KernelContracts kernels,
                                         Set<TypeSymbol.AtModule> constructedWithInvariants) {
        return switch (node) {
            case Core.Unreachable _ -> AbortSet.of(AbortKind.UNREACHABLE_REACHED);
            case Core.Binary b -> arithmetic(b);
            case Core.Neg n -> negation(n);
            case Core.Call c -> callAborts(c, kernels);
            case Core.Construct c -> constructedWithInvariants.contains(c.typeName())
                    ? AbortSet.of(AbortKind.INVARIANT_NOT_HELD)
                    : AbortSet.NONE;
            // A node the checker never lets carry a clause of its own to break, and never a
            // representation to run past the end of: a literal, a read, a unit or materialised
            // value, an already-tagged construction slot's parent, a fold, a tuple. What any of
            // these can end without a value for is answered by a child's own site, not by this one.
            case Core.Int _, Core.Decimal _, Core.Str _, Core.Bool _,
                    Core.Temporal _, Core.Read _, Core.UnitValue _,
                    Core.MaterialisedValue _, Core.OptionNone _,
                    Core.FieldAccess _, Core.PreservedCall _, Core.Apply _,
                    Core.If _, Core.IfConstructed _, Core.LetIn _,
                    Core.Block _, Core.ListLit _, Core.OptionSome _,
                    Core.Tuple _, Core.TupleGet _, Core.Match _, Core.Widen _ ->
                    AbortSet.NONE;
        };
    }

    /**
     * What a call reaching {@code call.fn()} can end without a value for.
     *
     * <p>A kernel call reads {@link KernelContracts}, the one place that answer is authored, rather
     * than a second reading of it here. A call to a declared behavior or a published value answers
     * {@link AbortSet#NONE} at this site: what the callee itself can end without a value for is a
     * fact about walking into that behavior's body, which is not this site's own — the same
     * distinction that keeps a subtree's abort set from being copied onto every node above it. A
     * value this module builds answers the same, for the same reason: its body is a root of its own.
     */
    private static AbortSet callAborts(Core.Call call, KernelContracts kernels) {
        return switch (call.fn()) {
            case Core.Reached.OfKernel kernel -> kernels.contractOf(kernel.kernel()).aborts();
            case Core.Reached.OfDeclaration _ -> AbortSet.NONE;
            case Core.Reached.OfValue _ -> AbortSet.NONE;
            case Core.Reached.OfPublishedValue _ -> AbortSet.NONE;
            // Minted by a Core-to-Core pass for a fold the backend lowers as a whole ($build,
            // $grow for a List or a Map); traced against souther-runtime's collection builders,
            // which raise nothing a Souther program can be given to overflow.
            case Core.Emitted _ -> AbortSet.NONE;
        };
    }

    /**
     * What {@code binary} — one of {@code + - * /} — can end a run without a value for, read off
     * {@link Core.Binary#type} rather than off an operand's: {@code type()} is the checked fact
     * {@code BodyGen} itself dispatches on ({@code bin.type() == Type.RATIONAL} selects
     * {@code RationalMath} ahead of the Int/Decimal arm), and an operand can name a different
     * runtime operation than the answer does — {@code Int / Int} runs {@code
     * RationalMath.divideWholeNumbers}, where both operands are {@code Int} and the answer, and the
     * operation, are {@code Rational}.
     *
     * <p>{@code +}, {@code -}, {@code *} abort only on {@link AbortKind#REQUIRED_FORM_HAS_NO_PLACE}:
     * an {@code Int} or a {@code Decimal} sum, difference or product outside what its type holds
     * ({@code souther.runtime.IntMath}, {@code souther.runtime.DecimalMath}), or a {@code Rational}
     * one whose required exact form asks for more exponent than {@code Rational} holds
     * ({@code souther.runtime.Rational#noRoomForIt}). Never both at one site: {@code Int + Int} and
     * {@code Decimal + Decimal} stay {@code Int} and {@code Decimal} (ADR-0116's homogeneous rule),
     * so a {@code +}/{@code -}/{@code *} whose answer is {@code Rational} already has a
     * {@code Rational}-typed operand feeding it — the same fact {@link #divide} reads directly for
     * {@code /}, which does not get that guarantee for free.
     */
    private static AbortSet arithmetic(Core.Binary binary) {
        return switch (binary.op()) {
            case BinOp.ADD, BinOp.SUB, BinOp.MUL -> arithmeticType(binary);
            case BinOp.DIV -> divide(binary);
            case BinOp.EQ, BinOp.NE, BinOp.LT, BinOp.LE, BinOp.GT, BinOp.GE, BinOp.AND, BinOp.OR,
                    BinOp.CONCAT ->
                    AbortSet.NONE;
        };
    }

    /** {@link AbortKind#REQUIRED_FORM_HAS_NO_PLACE} for every type {@code +}, {@code -} and
     *  {@code *} answer with, or a compiler invariant failure for a type none of them do — refused
     *  rather than answered with {@link AbortSet#NONE}, so a primitive the checker admits to
     *  arithmetic later and this has not been told about fails loudly instead of silently reading
     *  as total. */
    private static AbortSet arithmeticType(Core.Binary binary) {
        if (!(binary.type() instanceof Type.Prim prim)) {
            throw new IllegalStateException(
                    "`" + binary.op() + "` answers " + Type.show(binary.type())
                            + ", which no arithmetic the checker admits answers with");
        }
        return switch (prim) {
            case INT, DECIMAL, RATIONAL -> AbortSet.of(AbortKind.REQUIRED_FORM_HAS_NO_PLACE);
            case STRING, BOOL, DATE, TIME, DATETIME, INSTANT, RAW -> throw new IllegalStateException(
                    "`" + binary.op() + "` answers " + prim.shown()
                            + ", which no arithmetic the checker admits answers with");
        };
    }

    /**
     * Unary minus, read off {@link Core.Neg#type} the same way {@link #arithmeticType} reads
     * {@link Core.Binary#type} — the checked fact, not a re-derivation from what the backend happens
     * to emit. The specification states unary minus as answering the type it is given
     * (spec §an-operator-takes-the-types-it-is-defined-for) and states {@code Int}'s own case
     * explicitly: {@code abs} negates with {@code -}, and the smallest {@code Int} — the one value
     * with no positive counterpart — aborts on overflow like any other overflow (spec §stdlib-int).
     * {@code Decimal} and {@code Rational} negation only flip a sign; neither changes the scale or
     * the exponent a {@code +}/{@code -}/{@code *} on either type can push out of range, so neither
     * is a case {@link AbortKind#REQUIRED_FORM_HAS_NO_PLACE} names.
     *
     * <p>A checked {@code Core.Neg} answers only {@code Int}, {@code Decimal} or {@code Rational}
     * (spec §an-operator-takes-the-types-it-is-defined-for); a fourth reaching here is a malformed
     * checked {@code Core} and is refused the same way {@link #arithmeticType} refuses one, rather
     * than answered with {@link AbortSet#NONE}.
     */
    private static AbortSet negation(Core.Neg neg) {
        if (!(neg.type() instanceof Type.Prim prim)) {
            throw new IllegalStateException(
                    "unary minus answers " + Type.show(neg.type())
                            + ", which no negation the checker admits answers with");
        }
        return switch (prim) {
            case INT -> AbortSet.of(AbortKind.REQUIRED_FORM_HAS_NO_PLACE);
            case DECIMAL, RATIONAL -> AbortSet.NONE;
            case STRING, BOOL, DATE, TIME, DATETIME, INSTANT, RAW -> throw new IllegalStateException(
                    "unary minus answers " + prim.shown()
                            + ", which no negation the checker admits answers with");
        };
    }

    /**
     * {@code /}'s own answer is exact, and the exact quotient of any two of {@code Int},
     * {@code Decimal} and {@code Rational} is {@code Rational} (ADR-0116) — never {@code Int} or
     * {@code Decimal}, the way {@code +}, {@code -} and {@code *} can answer. {@code BodyGen} itself
     * has no kernel to reach for a {@code /} whose answer is not {@code Rational}: {@code
     * arithmetic(bin, null, null)} passes null for both, so a malformed one reaches the checker's
     * own "no kernel for this number" failure there. A {@code Core} the checker could not have
     * produced is refused here the same way, rather than answered as though it were an ordinary
     * {@code Int} or {@code Decimal} division — the one thing that would let a future checker
     * change quietly agree with a stale reading here.
     *
     * <p>{@code /} always answers {@code Rational}, but unlike {@code +}/{@code -}/{@code *} that
     * does not by itself mean a {@code Rational}-typed operand is already in play — {@code Int / Int}
     * and {@code Decimal / Decimal} answer {@code Rational} too. So this reads both operand types
     * directly, the one place in this walker an operand's own type decides the answer rather than
     * the node's. {@code BodyGen.pushExact} is why: {@code Int} and {@code Decimal} operands are
     * widened through {@code RationalMath.fromInt}/{@code fromDecimal} — exact and total, building a
     * fresh, compact {@code Rational} with no prior exponent history — while an operand already
     * {@code Rational}-typed is pushed as it stands, whatever exponents it already carries.
     * {@code Int / Int} is emitted through {@code RationalMath.divideWholeNumbers} specifically
     * (never the general path), but the same fact holds there too: two {@code long}s make a fresh,
     * compact pair.
     *
     * <p>So a zero divisor is the only reason where neither operand was already {@code Rational}:
     * {@code Int / Int} runs {@code divideWholeNumbers}, {@code Decimal / Decimal} runs
     * {@code RationalMath.divide} on two freshly-widened operands, and
     * {@code Rational#dividedBy}'s own exponent subtraction ({@code lessened}) cannot overflow a
     * {@code long} for exponents that both trace back to a 32-bit {@code Decimal} scale or a
     * {@code long} {@code Int} — traced directly against {@code Rational#dividedBy} rather than
     * assumed from the type alone. Where either operand is already {@code Rational}, it may carry
     * exponents from arithmetic earlier in the program, and dividing can still ask for more than
     * {@code Rational} holds.
     */
    private static AbortSet divide(Core.Binary binary) {
        if (binary.type() != Type.RATIONAL) {
            throw new IllegalStateException(
                    "`/` answers " + Type.show(binary.type()) + ", and the exact operator's answer"
                            + " is always Rational (spec §stdlib-rational)");
        }
        AbortSet zeroDivisor = AbortSet.of(AbortKind.DIVISION_BY_ZERO);
        boolean anOperandIsAlreadyRational =
                binary.left().type() == Type.RATIONAL || binary.right().type() == Type.RATIONAL;
        return anOperandIsAlreadyRational
                ? zeroDivisor.union(AbortSet.of(AbortKind.REQUIRED_FORM_HAS_NO_PLACE))
                : zeroDivisor;
    }
}
