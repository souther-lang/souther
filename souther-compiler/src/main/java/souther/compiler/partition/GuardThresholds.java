package souther.compiler.partition;

import souther.compiler.ast.Ast;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.diag.SourceRef;
import souther.compiler.types.Type;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.List;

/**
 * The values a behavior's body compares its inputs against.
 *
 * <p>A model's own thresholds, read where they are written. "Pre-approval is needed at a hundred
 * thousand" is not in any type — it is the comparison the behavior makes — and it is the line the
 * rows have to be written on both sides of.
 *
 * <p><b>Only a condition that is itself a comparison is read.</b> Nothing recurses into {@code &&},
 * {@code ||} or {@code !}. The reason is short-circuiting: in
 *
 * <pre>if kind == Domestic &amp;&amp; cost &lt;= 100000</pre>
 *
 * an overseas request takes the else arm without {@code cost} ever being compared, so a row that
 * lands there is not a boundary test of {@code cost} and counting it as one would report a boundary
 * covered that nothing exercised. Reading compound conditions needs a probe on each comparison rather
 * than on each arm, which is a larger change than this one; until then the restriction is stated and
 * the thresholds inside a compound condition are simply not read.
 */
public final class GuardThresholds {

    /** The thresholds one behavior's body compares its parameters against. {@code plan} supplies the
     * guard each one belongs to, so a boundary can later ask whether the comparison ran. */
    public static List<Threshold> of(String behavior, Core body, CoverageSites.Plan plan,
                                     List<String> parameters, Symbols symbols) {
        List<Threshold> found = new ArrayList<>();
        walk(behavior, body, plan, parameters, symbols, found);
        return List.copyOf(found);
    }

    private static void walk(String behavior, Core e, CoverageSites.Plan plan,
                             List<String> parameters, Symbols symbols, List<Threshold> out) {
        if (e instanceof Core.If iff) {
            read(behavior, iff, plan, parameters, symbols).ifPresent(out::add);
        }
        // A match case's body and an attempted construction's departure are expression slots, so the
        // generic walk reaches them; only the arms themselves are not children, and this walk does not
        // number arms.
        Core.forEachChild(e, child -> walk(behavior, child, plan, parameters, symbols, out));
    }

    private static java.util.Optional<Threshold> read(String behavior, Core.If iff,
                                                      CoverageSites.Plan plan,
                                                      List<String> parameters, Symbols symbols) {
        if (!(iff.cond() instanceof Core.Binary comparison)) {
            return java.util.Optional.empty();
        }
        Ast.BinOp op = comparison.op();
        TermPath path = pathOf(comparison.left(), parameters, symbols);
        BigDecimal value = constantOf(comparison.right());
        if (path == null || value == null) {
            // `100000 >= cost` says what `cost <= 100000` says; read the position-bearing side first.
            path = pathOf(comparison.right(), parameters, symbols);
            value = constantOf(comparison.left());
            op = mirrored(op);
        }
        if (path == null || value == null) {
            return java.util.Optional.empty();
        }
        Boolean below = switch (op) {
            case LE, GT -> Boolean.TRUE;    // the value itself is on the low side
            case LT, GE -> Boolean.FALSE;   // and here it is on the high side
            default -> null;                // EQ / NE do not order the values, so they draw no cut
        };
        if (below == null) {
            return java.util.Optional.empty();
        }
        CoverageSites.GuardRef guard = guardOf(plan, iff);
        if (guard == null) {
            return java.util.Optional.empty();   // no site for this `if`: nothing could answer for it
        }
        return java.util.Optional.of(new Threshold(path, value, below,
                new OriginRef.GuardOrigin(guard, new SourceRef(guard.at().sourceId(), iff.pos()),
                        below)));
    }

    private static CoverageSites.GuardRef guardOf(CoverageSites.Plan plan, Core.If iff) {
        int[] arms = plan.probesOf(iff);
        if (arms == null || arms.length != 2) {
            return null;
        }
        for (CoverageSites.GuardRef guard : plan.guards()) {
            if (guard.siteIndexThen() == arms[0] && guard.siteIndexElse() == arms[1]) {
                return guard;
            }
        }
        return null;
    }

    /**
     * The input position a comparison names, spelled the way a parameter's own path is spelled.
     *
     * <p>A newtype's {@code value} is not a step: {@code request.cost} and {@code request.cost.value}
     * are one location, and if the two spellings disagreed the same position would become two axes,
     * one of which no row would ever cover. This is the rule {@code InvariantChecker} follows over the
     * surface tree; the same rule, over the tree the checker produced.
     */
    static TermPath pathOf(Core e, List<String> parameters, Symbols symbols) {
        return switch (e) {
            case Core.Read r -> parameters.contains(r.name()) ? TermPath.of(r.name()) : null;
            case Core.FieldAccess fa -> {
                TermPath base = pathOf(fa.target(), parameters, symbols);
                if (base == null) {
                    yield null;
                }
                yield fa.field().equals("value")
                        && TypeOps.isSingleValueNewtype(fa.target().type(), symbols)
                        ? base : base.then(fa.field());
            }
            case null, default -> null;
        };
    }

    /** The number a comparison is against, or null where the other side is not one. */
    static BigDecimal constantOf(Core e) {
        return switch (e) {
            case Core.Int i -> BigDecimal.valueOf(i.value());
            case Core.Decimal d -> d.value();
            case Core.Neg n -> {
                BigDecimal inner = constantOf(n.operand());
                yield inner == null ? null : inner.negate();
            }
            // A newtype written around a constant is that constant at this location.
            case Core.NewData nd when nd.inits().size() == 1 && nd.spreads().isEmpty() ->
                    constantOf(nd.inits().get(0).value());
            case null, default -> null;
        };
    }

    private static Ast.BinOp mirrored(Ast.BinOp op) {
        return switch (op) {
            case LT -> Ast.BinOp.GT;
            case LE -> Ast.BinOp.GE;
            case GT -> Ast.BinOp.LT;
            case GE -> Ast.BinOp.LE;
            default -> op;
        };
    }

    /** Whether a type is one whose values a threshold can order. */
    static boolean orderable(Type type, Symbols symbols) {
        Type base = TypeOps.base(type, symbols);
        return base == Type.INT || base == Type.DECIMAL;
    }

    private GuardThresholds() {}
}
