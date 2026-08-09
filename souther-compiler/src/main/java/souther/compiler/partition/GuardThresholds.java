package souther.compiler.partition;

import souther.compiler.ast.Ast;
import souther.compiler.check.Location;
import souther.compiler.check.NumericMeasures;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.diag.SourceRef;
import souther.compiler.types.ReachName;
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

    /**
     * What one reading of a body says about the comparisons in it.
     *
     * <p>Two answers from one walk, because they are read off the same comparison and the operator is
     * known once. Asked separately they would be two readings of it, and the second would have to
     * recover from {@link Threshold} which side of the line each arm takes — which a threshold does not
     * say and cannot be made to say (see {@link GuardEdge}).
     */
    public record Guards(List<Threshold> thresholds, List<GuardEdge> edges) {

        public static final Guards NONE = new Guards(List.of(), List.of());

        public Guards {
            thresholds = List.copyOf(thresholds);
            edges = List.copyOf(edges);
        }
    }

    /** The thresholds one behavior's body compares its parameters against, and both arms of each
     * comparison. {@code plan} supplies the guard each one belongs to, so a boundary can later ask
     * whether the comparison ran and an arm can be found by the probe that counts it. */
    public static Guards of(String behavior, Core body, CoverageSites.Plan plan,
                            List<String> parameters, Symbols symbols) {
        List<Threshold> found = new ArrayList<>();
        List<GuardEdge> edges = new ArrayList<>();
        walk(behavior, body, plan, parameters, symbols, found, edges);
        return new Guards(found, edges);
    }

    private static void walk(String behavior, Core e, CoverageSites.Plan plan,
                             List<String> parameters, Symbols symbols, List<Threshold> out,
                             List<GuardEdge> edges) {
        if (e instanceof Core.If iff) {
            read(behavior, iff, plan, parameters, symbols, out, edges);
        }
        // A match case's body and an attempted construction's departure are expression slots, so the
        // generic walk reaches them; only the arms themselves are not children, and this walk does not
        // number arms.
        Core.forEachChild(e, child -> walk(behavior, child, plan, parameters, symbols, out, edges));
    }

    private static void read(String behavior, Core.If iff, CoverageSites.Plan plan,
                             List<String> parameters, Symbols symbols, List<Threshold> out,
                             List<GuardEdge> edges) {
        if (!(iff.cond() instanceof Core.Binary comparison)) {
            return;
        }
        Ast.BinOp op = comparison.op();
        NumericTerm term = termOf(comparison.left(), parameters, symbols);
        BigDecimal value = constantOf(comparison.right());
        if (term == null || value == null) {
            // `100000 >= cost` says what `cost <= 100000` says; read the position-bearing side first.
            term = termOf(comparison.right(), parameters, symbols);
            value = constantOf(comparison.left());
            op = mirrored(op);
        }
        if (term == null || value == null) {
            return;
        }
        Boolean below = switch (op) {
            case LE, GT -> Boolean.TRUE;    // the value itself is on the low side
            case LT, GE -> Boolean.FALSE;   // and here it is on the high side
            default -> null;                // EQ / NE do not order the values, so they draw no cut
        };
        if (below == null) {
            return;
        }
        CoverageSites.GuardRef guard = guardOf(plan, iff);
        if (guard == null) {
            return;   // no site for this `if`: nothing could answer for it
        }
        out.add(new Threshold(term, value, below,
                new OriginRef.GuardOrigin(guard, new SourceRef(guard.at().sourceId(), iff.pos()),
                        below)));
        // Which side of the line the line's own value is on does not say which arm is which. `x <= c`
        // and `x > c` agree about the first and take opposite halves, so the arms are read off the
        // operator here, where it is still known, and not recovered from the threshold later.
        int then = guard.siteIndexThen();
        int otherwise = guard.siteIndexElse();
        switch (op) {
            case LE -> {
                edge(edges, guard, then, term, value, true, true);
                edge(edges, guard, otherwise, term, value, false, false);
            }
            case GT -> {
                edge(edges, guard, then, term, value, false, false);
                edge(edges, guard, otherwise, term, value, true, true);
            }
            case LT -> {
                edge(edges, guard, then, term, value, true, false);
                edge(edges, guard, otherwise, term, value, false, true);
            }
            case GE -> {
                edge(edges, guard, then, term, value, false, true);
                edge(edges, guard, otherwise, term, value, true, false);
            }
            default -> { }
        }
    }

    /** One arm's edge, where that arm has a probe. An arm answering nothing has none, and it is owed
     * no row whether anything reaches it or not. */
    private static void edge(List<GuardEdge> edges, CoverageSites.GuardRef guard, int site,
                             NumericTerm term, BigDecimal value, boolean below, boolean inclusive) {
        if (site == CoverageSites.NO_SITE) {
            return;
        }
        edges.add(below ? GuardEdge.below(guard, site, term, value, inclusive)
                : GuardEdge.above(guard, site, term, value, inclusive));
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
     * <p>Which fields are steps is {@link Location}'s rule, asked here rather than restated: a
     * newtype's {@code value} is not one, so {@code request.cost} and {@code request.cost.value} are
     * one position, and if the two spellings disagreed the same position would become two axes, one
     * of which no row would ever cover.
     *
     * <p>The root is not that rule's. A partition is derived from what a behavior declares, and a
     * declared parameter is not a binding — a behavior with no implementation has axes all the same —
     * so this path is rooted at the parameter and {@link Location} at the binding a body gave it.
     */
    /**
     * The number a comparison names, which is a location's content or something taken of it.
     *
     * <p>Which of the standard library's calls count is asked of {@link NumericMeasures} rather than
     * decided here, and asked of the operation the call resolved to rather than of its spelling. The
     * argument has to be a location: {@code List.length(List.map(f, xs))} counts something no path
     * names, and a boundary on it could not be looked for in a row.
     */
    static NumericTerm termOf(Core e, List<String> parameters, Symbols symbols) {
        if (e instanceof Core.Call call && call.fn() instanceof Core.Reached reached
                && reached.name() instanceof ReachName.OfLibrary library
                && NumericMeasures.isMeasure(library.target()) && call.args().size() == 1) {
            TermPath of = pathOf(call.args().get(0), parameters, symbols);
            return of == null ? null : new NumericTerm.SizeOf(library.target(), of);
        }
        TermPath path = pathOf(e, parameters, symbols);
        return path == null ? null : new NumericTerm.ValueOf(path);
    }

    static TermPath pathOf(Core e, List<String> parameters, Symbols symbols) {
        return switch (e) {
            case Core.Read r -> parameters.contains(r.name()) ? TermPath.of(r.name()) : null;
            case Core.FieldAccess fa -> {
                TermPath base = pathOf(fa.target(), parameters, symbols);
                if (base == null) {
                    yield null;
                }
                yield Location.isStep(fa.target().type(), fa.field(), symbols)
                        ? base.then(fa.field()) : base;
            }
            // A call kept standing names no location, and its presence says this walk was handed a
            // representation it does not read. Said rather than answered with "no path", which would
            // be the same answer a number gives.
            case Core.PreservedCall p -> throw p.unexpectedIn("guard thresholds");
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
