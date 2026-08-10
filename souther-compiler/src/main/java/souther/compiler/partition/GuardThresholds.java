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
    public record Guards(List<Threshold> thresholds, List<GuardEdge> edges,
                         List<TermPath> unread) {

        public static final Guards NONE = new Guards(List.of(), List.of(), List.of());

        public Guards {
            thresholds = List.copyOf(thresholds);
            edges = List.copyOf(edges);
            unread = List.copyOf(unread);
        }
    }

    /** The thresholds one behavior's body compares its parameters against, and both arms of each
     * comparison. {@code plan} supplies the guard each one belongs to, so a boundary can later ask
     * whether the comparison ran and an arm can be found by the probe that counts it. */
    public static Guards of(String behavior, Core body, CoverageSites.Plan plan,
                            List<String> parameters, Symbols symbols) {
        List<Threshold> found = new ArrayList<>();
        List<GuardEdge> edges = new ArrayList<>();
        List<TermPath> unread = new ArrayList<>();
        walk(behavior, body, plan, parameters, symbols, found, edges, unread);
        return new Guards(found, edges, unread);
    }

    private static void walk(String behavior, Core e, CoverageSites.Plan plan,
                             List<String> parameters, Symbols symbols, List<Threshold> out,
                             List<GuardEdge> edges, List<TermPath> unread) {
        if (e instanceof Core.If iff) {
            List<TermPath> made = read(behavior, iff, plan, parameters, symbols, out, edges);
            // Every position this condition compares, less the one a line was drawn on. What is left
            // is a rule the model states here and this did not read, which is the one thing that
            // keeps a later reader from taking an empty list for a model that says nothing.
            for (TermPath compared : comparedIn(iff.cond(), parameters, symbols)) {
                if (!made.contains(compared) && !unread.contains(compared)) {
                    unread.add(compared);
                }
            }
        }
        // A match case's body and an attempted construction's departure are expression slots, so the
        // generic walk reaches them; only the arms themselves are not children, and this walk does not
        // number arms.
        Core.forEachChild(e,
                child -> walk(behavior, child, plan, parameters, symbols, out, edges, unread));
    }

    /**
     * Every position a condition compares, however the condition is written.
     *
     * <p>Names them and no more. What a comparison inside a conjunction would need before it could be
     * a line is which arm witnesses it having been evaluated, and that is not answered here — a
     * threshold recorded without it is an obligation nobody can discharge. So this establishes only
     * that the model draws something at this position, which is exactly what {@code not derivable}
     * would otherwise deny.
     */
    private static List<TermPath> comparedIn(Core e, List<String> parameters, Symbols symbols) {
        List<TermPath> out = new ArrayList<>();
        compared(e, parameters, symbols, out);
        return out;
    }

    private static void compared(Core e, List<String> parameters, Symbols symbols,
                                 List<TermPath> out) {
        if (e instanceof Core.Binary binary && orders(binary.op())) {
            for (Core side : List.of(binary.left(), binary.right())) {
                NumericTerm named = termOf(side, parameters, symbols);
                if (named != null && !out.contains(named.path())) {
                    out.add(named.path());
                }
            }
        }
        Core.forEachChild(e, child -> compared(child, parameters, symbols, out));
    }

    /** Whether an operator is one that compares two values rather than combining two conditions. */
    private static boolean orders(Ast.BinOp op) {
        return switch (op) {
            case EQ, NE, LT, LE, GT, GE -> true;
            case AND, OR, ADD, SUB, MUL, DIV, CONCAT -> false;
        };
    }

    /**
     * The positions a line was drawn on here.
     *
     * <p>One condition can hold several. {@code A && B} is two comparisons and two lines, and which
     * arm stands as evidence for each is not the same answer — so each is read with the witness its
     * place in the condition leaves it, and the arms are numbered once for the {@code if} they both
     * belong to.
     */
    private static List<TermPath> read(String behavior, Core.If iff, CoverageSites.Plan plan,
                                       List<String> parameters, Symbols symbols,
                                       List<Threshold> out, List<GuardEdge> edges) {
        List<TermPath> made = new ArrayList<>();
        for (Placed each : comparisonsIn(iff.cond())) {
            TermPath here = readOne(behavior, iff, each, plan, parameters, symbols, out, edges);
            if (here != null) {
                made.add(here);
            }
        }
        return made;
    }

    /** One comparison of a condition, and which arms of the {@code if} prove it was evaluated. */
    private record Placed(Core.Binary comparison, OriginRef.GuardOrigin.Witness witness) {}

    /**
     * The comparisons a condition is made of, each with what its place leaves as evidence.
     *
     * <p>The leftmost is always evaluated, whatever the condition is made of. Past that it depends on
     * what combines them: under a condition that is nothing but {@code &&}, reaching the arm where
     * the whole thing held proves every operand was evaluated and true; under nothing but
     * {@code ||}, the arm where it did not hold does. A condition mixing the two leaves neither arm
     * separating the rows that reached a comparison from the rows that did not, and that is said
     * rather than guessed at — the line is still the model's, and only the evidence is missing.
     */
    private static List<Placed> comparisonsIn(Core condition) {
        List<Core> leaves = new ArrayList<>();
        List<Ast.BinOp> combining = new ArrayList<>();
        flatten(condition, leaves, combining);
        OriginRef.GuardOrigin.Witness past = combining.isEmpty()
                ? OriginRef.GuardOrigin.Witness.BOTH
                : combining.stream().allMatch(op -> op == Ast.BinOp.AND)
                        ? OriginRef.GuardOrigin.Witness.THEN
                        : combining.stream().allMatch(op -> op == Ast.BinOp.OR)
                                ? OriginRef.GuardOrigin.Witness.ELSE
                                : OriginRef.GuardOrigin.Witness.NEITHER;
        List<Placed> out = new ArrayList<>();
        for (int i = 0; i < leaves.size(); i++) {
            if (leaves.get(i) instanceof Core.Binary binary && !combines(binary.op())) {
                out.add(new Placed(binary, i == 0 ? OriginRef.GuardOrigin.Witness.BOTH : past));
            }
        }
        return out;
    }

    /** The operands of a condition, left to right, and the operators holding them together. */
    private static void flatten(Core e, List<Core> leaves, List<Ast.BinOp> combining) {
        if (e instanceof Core.Binary binary && combines(binary.op())) {
            combining.add(binary.op());
            flatten(binary.left(), leaves, combining);
            flatten(binary.right(), leaves, combining);
            return;
        }
        leaves.add(e);
    }

    private static boolean combines(Ast.BinOp op) {
        return op == Ast.BinOp.AND || op == Ast.BinOp.OR;
    }

    /** The position a line was drawn on by one comparison, or null where none was. */
    private static TermPath readOne(String behavior, Core.If iff, Placed placed,
                                    CoverageSites.Plan plan, List<String> parameters,
                                    Symbols symbols, List<Threshold> out, List<GuardEdge> edges) {
        Core.Binary comparison = placed.comparison();
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
            return null;
        }
        Boolean below = switch (op) {
            case LE, GT -> Boolean.TRUE;    // the value itself is on the low side
            case LT, GE -> Boolean.FALSE;   // and here it is on the high side
            default -> null;                // EQ / NE do not order the values, so they draw no cut
        };
        if (below == null) {
            return null;
        }
        CoverageSites.GuardRef guard = guardOf(plan, iff);
        if (guard == null) {
            return null;   // no site for this `if`: nothing could answer for it
        }
        // True at the line's own value for the operators that include it, which is not the same
        // question as which class the value falls in: `x <= c` and `x > c` agree about the second.
        boolean holds = op == Ast.BinOp.LE || op == Ast.BinOp.GE;
        out.add(new Threshold(term, value, below,
                new OriginRef.GuardOrigin(guard, new SourceRef(guard.at().sourceId(), iff.pos()),
                        below, placed.witness(), holds)));
        // Which side of the line the line's own value is on does not say which arm is which. `x <= c`
        // and `x > c` agree about the first and take opposite halves, so the arms are read off the
        // operator here, where it is still known, and not recovered from the threshold later.
        // An arm that does not witness this comparison is not one of its edges either: what reaches
        // it is decided by the rest of the condition as much as by this line.
        int then = placed.witness() == OriginRef.GuardOrigin.Witness.ELSE
                || placed.witness() == OriginRef.GuardOrigin.Witness.NEITHER
                        ? CoverageSites.NO_SITE : guard.siteIndexThen();
        int otherwise = placed.witness() == OriginRef.GuardOrigin.Witness.THEN
                || placed.witness() == OriginRef.GuardOrigin.Witness.NEITHER
                        ? CoverageSites.NO_SITE : guard.siteIndexElse();
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
        return term.path();
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
            // A date written the way a model writes one. Read by what the construction answers with
            // rather than by the name in front of it, so a date reaches this however it is spelled.
            case Core.Call call when call.type() == Type.DATE && call.args().size() == 1
                    && call.args().get(0) instanceof Core.Str iso -> Dates.dayOf(iso.value());
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
        return base == Type.INT || base == Type.DECIMAL || base == Type.DATE;
    }

    private GuardThresholds() {}
}
