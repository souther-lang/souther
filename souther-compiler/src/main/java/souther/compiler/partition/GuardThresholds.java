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
                         List<Unread> unread, List<Singled> singled) {

        public static final Guards NONE =
                new Guards(List.of(), List.of(), List.of(), List.of());

        /**
         * A value a body singles out rather than orders.
         *
         * <p>Apart from a {@link Threshold}, which says where one range ends and the next begins. An
         * equality says nothing about ranges: what it distinguishes is the value from every other
         * value, and reading it as a place to cut would put a distinction between the two sides into
         * a partition the model never drew.
         */
        public record Singled(NumericTerm term, BigDecimal value, OriginRef.GuardOrigin origin) {}

        /** A position a comparison names that this did not turn into a line, and what stopped it. */
        public record Unread(TermPath at, UndividedPosition.Reason why) {}

        public Guards {
            thresholds = List.copyOf(thresholds);
            edges = List.copyOf(edges);
            unread = List.copyOf(unread);
            singled = List.copyOf(singled);
        }
    }

    /** The thresholds one behavior's body compares its parameters against, and both arms of each
     * comparison. {@code plan} supplies the guard each one belongs to, so a boundary can later ask
     * whether the comparison ran and an arm can be found by the probe that counts it. */
    public static Guards of(String behavior, Core body, CoverageSites.Plan plan,
                            List<String> parameters, Symbols symbols) {
        List<Threshold> found = new ArrayList<>();
        List<GuardEdge> edges = new ArrayList<>();
        List<Guards.Unread> unread = new ArrayList<>();
        List<Guards.Singled> singled = new ArrayList<>();
        walk(behavior, body, plan, parameters, symbols, found, edges, unread, singled);
        return new Guards(found, edges, unread, singled);
    }

    private static void walk(String behavior, Core e, CoverageSites.Plan plan,
                             List<String> parameters, Symbols symbols, List<Threshold> out,
                             List<GuardEdge> edges, List<Guards.Unread> unread,
                             List<Guards.Singled> singled) {
        if (e instanceof Core.If iff) {
            List<TermPath> made =
                    read(behavior, iff, plan, parameters, symbols, out, edges, singled);
            // Every position this condition compares, less the one a line was drawn on. What is left
            // is a rule the model states here and this did not read, which is the one thing that
            // keeps a later reader from taking an empty list for a model that says nothing.
            for (Guards.Unread compared : comparedIn(iff.cond(), parameters, symbols)) {
                if (!made.contains(compared.at())
                        && unread.stream().noneMatch(had -> had.at().equals(compared.at()))) {
                    unread.add(compared);
                }
            }
        }
        // A match case's body and an attempted construction's departure are expression slots, so the
        // generic walk reaches them; only the arms themselves are not children, and this walk does not
        // number arms.
        Core.forEachChild(e, child ->
                walk(behavior, child, plan, parameters, symbols, out, edges, unread, singled));
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
    private static List<Guards.Unread> comparedIn(Core e, List<String> parameters, Symbols symbols) {
        List<Guards.Unread> out = new ArrayList<>();
        compared(e, parameters, symbols, out);
        return out;
    }

    private static void compared(Core e, List<String> parameters, Symbols symbols,
                                 List<Guards.Unread> out) {
        if (e instanceof Core.Binary binary && orders(binary.op())) {
            for (Core side : List.of(binary.left(), binary.right())) {
                NumericTerm named = termOf(side, parameters, symbols);
                if (named != null && out.stream().noneMatch(had -> had.at().equals(named.path()))) {
                    out.add(new Guards.Unread(named.path(), why(binary)));
                }
            }
        }
        Core.forEachChild(e, child -> compared(child, parameters, symbols, out));
    }

    /**
     * What would have to change before this comparison could be a line.
     *
     * <p>Two different things, and a reader told one sentence for both cannot tell which limit is
     * theirs to wait on. A comparison against something that is not a number this carries asks for a
     * carrier; what is left is a condition this does not take apart.
     */
    private static UndividedPosition.Reason why(Core.Binary comparison) {
        // The carrier first. An equality divides the values wherever it is written — the value and
        // everything else — so what is missing at a position it did not divide is a number to draw
        // the line at, whatever the operator was.
        return constantOf(comparison.left()) == null && constantOf(comparison.right()) == null
                ? UndividedPosition.Reason.UNSUPPORTED_DOMAIN
                : UndividedPosition.Reason.UNSUPPORTED_SYNTAX;
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
                                       List<Threshold> out, List<GuardEdge> edges,
                                       List<Guards.Singled> singled) {
        List<TermPath> made = new ArrayList<>();
        for (Placed each : comparisonsIn(iff.cond())) {
            TermPath here =
                    readOne(behavior, iff, each, plan, parameters, symbols, out, edges, singled);
            if (here != null) {
                made.add(here);
            }
        }
        return made;
    }

    /** One comparison of a condition, and which arms of the {@code if} prove it was evaluated. */
    private record Placed(Core.Binary comparison, OriginRef.GuardOrigin.Witness witness) {}

    /**
     * The comparisons a condition is made of, each with what its own place leaves as evidence.
     *
     * <p>Asked per comparison and not per condition. A condition that is nothing but {@code &&}
     * settles it for every operand at once, and so does one that is nothing but {@code ||}; a
     * condition made of both does not. In {@code A && (B || C)} the arm where the whole thing held
     * proves {@code A} was true and so proves {@code B} ran, while {@code C} ran only where
     * {@code B} was false — which is a difference between two operands of one condition, and a
     * single verdict over the whole cannot hold it.
     *
     * <p>Two facts are carried down, and they are not the same one. Whether this subtree is
     * evaluated at all on a given arm, and whether reaching that arm forces the subtree's own value
     * — because it is the second that says whether the operand to its left was true, which is what
     * decides whether the operand to its right ran.
     */
    private static List<Placed> comparisonsIn(Core condition) {
        List<Placed> out = new ArrayList<>();
        // At the top there is nothing above to have stopped the condition, and the arm taken is the
        // condition's own value.
        placed(condition, new Reached(true, true, true, true), out);
        return out;
    }

    /**
     * What reaching each arm of the enclosing {@code if} says about one subtree of its condition.
     *
     * @param onThen    whether reaching the {@code then} arm implies this subtree was evaluated
     * @param onElse    the same for {@code else}
     * @param trueThen  whether reaching {@code then} implies this subtree's own value was true
     * @param falseElse whether reaching {@code else} implies its own value was false
     */
    private record Reached(boolean onThen, boolean onElse, boolean trueThen, boolean falseElse) {

        OriginRef.GuardOrigin.Witness witness() {
            if (onThen && onElse) {
                return OriginRef.GuardOrigin.Witness.BOTH;
            }
            if (onThen) {
                return OriginRef.GuardOrigin.Witness.THEN;
            }
            return onElse ? OriginRef.GuardOrigin.Witness.ELSE
                    : OriginRef.GuardOrigin.Witness.NEITHER;
        }
    }

    private static boolean combines(Ast.BinOp op) {
        return op == Ast.BinOp.AND || op == Ast.BinOp.OR;
    }

    private static void placed(Core e, Reached reached, List<Placed> out) {
        if (e instanceof Core.Binary binary && combines(binary.op())) {
            boolean and = binary.op() == Ast.BinOp.AND;
            // A conjunction's value being true makes both its operands true; a disjunction's being
            // false makes both false. Neither says anything the other way round.
            Reached left = new Reached(reached.onThen(), reached.onElse(),
                    and && reached.trueThen(), !and && reached.falseElse());
            // The right operand runs where the left settled nothing — which is where the left was
            // true under `&&` and false under `||`, and that is what the left's own forced value
            // above says.
            Reached right = new Reached(
                    and && reached.onThen() && reached.trueThen(),
                    !and && reached.onElse() && reached.falseElse(),
                    and && reached.trueThen(), !and && reached.falseElse());
            placed(binary.left(), left, out);
            placed(binary.right(), right, out);
            return;
        }
        if (e instanceof Core.Binary comparison && !combines(comparison.op())) {
            out.add(new Placed(comparison, reached.witness()));
        }
    }


    /** The position a line was drawn on by one comparison, or null where none was. */
    private static TermPath readOne(String behavior, Core.If iff, Placed placed,
                                    CoverageSites.Plan plan, List<String> parameters,
                                    Symbols symbols, List<Threshold> out, List<GuardEdge> edges,
                                    List<Guards.Singled> singled) {
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
            default -> null;                // EQ / NE do not order the values, so they cut nothing
        };
        CoverageSites.GuardRef guard = guardOf(plan, iff);
        if (guard == null) {
            return null;   // no site for this `if`: nothing could answer for it
        }
        if (below == null) {
            // An equality singles the value out instead. Recorded as that rather than as a place to
            // cut, because the values either side of it are not a distinction the model has drawn.
            if (op != Ast.BinOp.EQ && op != Ast.BinOp.NE) {
                return null;
            }
            singled.add(new Guards.Singled(term, value,
                    new OriginRef.GuardOrigin(guard, new SourceRef(guard.at().sourceId(), iff.pos()),
                            true, placed.witness(), op == Ast.BinOp.EQ, true)));
            return term.path();
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
