package souther.compiler.partition;

import souther.compiler.ast.Ast;
import souther.compiler.check.Location;
import souther.compiler.check.NumericMeasures;
import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;
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
 * <p><b>A comparison is read wherever in a condition it is written</b> (spec
 * §boundary-coordinates). Which position the model divides is not a question about the
 * shape of the condition around the comparison, and it was answered as though it were: in
 *
 * <pre>if kind == Domestic &amp;&amp; cost &lt;= 100000</pre>
 *
 * the line at a hundred thousand went unread, and the position came back as one the model divides
 * no way — two tokens from the comparison that divides it.
 *
 * <p>Whether a comparison ran is not something the arms answer. A condition stops as soon as it is
 * settled, so under {@code A && B} an overseas request takes the else arm without {@code cost} having
 * been compared — and so does a request whose cost was compared and found too high. Each comparison
 * carries the site its own value is recorded at, which is what a line is measured against. What the
 * shape of the condition does decide is which arm a row that reached the comparison can be in, and
 * that is a question about the classes either side of the line: it is carried as a {@link OriginRef
 * .GuardOrigin.Witness} and read by {@link GuardEdge}.
 *
 * <p>Three readers are kept apart here and are easy to run together. Which comparisons exist is
 * {@link #comparisonsIn}; which positions a comparison names at all is {@link #mentioned}; which
 * number a line can be drawn on is {@link #termOf}. The last is the narrowest, and asking it the
 * first two questions is how a position a body compares became a position nothing compares.
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
                         List<UnreadRule> unread, List<Singled> singled,
                         List<BoundaryObligation> between) {

        public static final Guards NONE =
                new Guards(List.of(), List.of(), List.of(), List.of(), List.of());

        /**
         * A value a body singles out rather than orders.
         *
         * <p>Apart from a {@link Threshold}, which says where one range ends and the next begins. An
         * equality says nothing about ranges: what it distinguishes is the value from every other
         * value, and reading it as a place to cut would put a distinction between the two sides into
         * a partition the model never drew.
         */
        public record Singled(NumericTerm term, Place value, OriginRef.GuardOrigin origin) {}

        public Guards {
            thresholds = List.copyOf(thresholds);
            edges = List.copyOf(edges);
            unread = List.copyOf(unread);
            singled = List.copyOf(singled);
            between = List.copyOf(between);
        }
    }

    /** The thresholds one behavior's body compares its parameters against, and both arms of each
     * comparison. {@code plan} supplies the guard each one belongs to, so a boundary can later ask
     * whether the comparison ran and an arm can be found by the probe that counts it. */
    public static Guards of(String behavior, Core body, CoverageSites.Plan plan,
                            List<String> parameters, Symbols symbols) {
        List<Threshold> found = new ArrayList<>();
        List<GuardEdge> edges = new ArrayList<>();
        List<UnreadRule> unread = new ArrayList<>();
        List<Guards.Singled> singled = new ArrayList<>();
        List<BoundaryObligation> between = new ArrayList<>();
        walk(behavior, body, plan, parameters, symbols, found, edges, unread, singled, between);
        return new Guards(found, edges, unread, singled, between);
    }

    private static void walk(String behavior, Core e, CoverageSites.Plan plan,
                             List<String> parameters, Symbols symbols, List<Threshold> out,
                             List<GuardEdge> edges, List<UnreadRule> unread,
                             List<Guards.Singled> singled, List<BoundaryObligation> between) {
        if (e instanceof Core.If iff) {
            List<Core> read =
                    read(behavior, iff, plan, parameters, symbols, out, edges, singled, between);
            // Every comparison this condition holds that nothing turned into a line — asked of the
            // comparisons and not of the positions. One position carries more than one statement,
            // and a line read at it says nothing about the rest: kept per position, a threshold on
            // `x` swallowed the comparison beside it that nothing could read, which is "a result
            // exists, so the reading is complete".
            for (UnreadRule compared : comparedIn(iff.cond(), read, parameters, symbols)) {
                if (unread.stream().noneMatch(had -> had.equals(compared))) {
                    unread.add(compared);
                }
            }
        }
        // A match case's body and an attempted construction's departure are expression slots, so the
        // generic walk reaches them; only the arms themselves are not children, and this walk does not
        // number arms.
        Core.forEachChild(e, child -> walk(behavior, child, plan, parameters, symbols, out, edges,
                unread, singled, between));
    }

    /**
     * Every position a condition compares, however the condition is written.
     *
     * <p>Names them and no more. Whether a line can be drawn on one is {@link #termOf}'s narrower
     * question, and this establishes only that the model draws something at this position — which is
     * exactly what {@code not derivable} would otherwise deny.
     */
    private static List<UnreadRule> comparedIn(Core e, List<Core> read, List<String> parameters,
                                               Symbols symbols) {
        List<UnreadRule> out = new ArrayList<>();
        compared(e, read, parameters, symbols, out);
        return out;
    }

    private static void compared(Core e, List<Core> read, List<String> parameters, Symbols symbols,
                                 List<UnreadRule> out) {
        // By the comparison it is, and not by what it was about: two comparisons at one position are
        // two statements, and this one having been read is no answer about the other.
        if (e instanceof Core.Binary comparison && orders(comparison.op())
                && read.stream().anyMatch(each -> each == comparison)) {
            return;
        }
        if (e instanceof Core.Binary binary && orders(binary.op())) {
            List<TermPath> named = new ArrayList<>();
            mentioned(binary.left(), parameters, symbols, named);
            mentioned(binary.right(), parameters, symbols, named);
            BlockReason why = why(binary, parameters, symbols);
            for (TermPath each : named) {
                if (out.stream().noneMatch(had -> had.at().equals(each))) {
                    out.add(new UnreadRule(each, why));
                }
            }
        }
        Core.forEachChild(e, child -> compared(child, read, parameters, symbols, out));
    }

    /**
     * Every position an expression names, however it is written.
     *
     * <p>Weaker than {@link #termOf} on purpose, and asked instead of it. That one answers whether a
     * line can be drawn — it wants a number the terms name — and this one answers whether the model
     * says anything about a position at all. Sharing a reader between the two turns an expression
     * the derivation does not model into a position nothing compares: {@code p.x + 1 < 10} named no
     * position, and came back as one the model divides no way two tokens from a comparison about it.
     */
    private static void mentioned(Core e, List<String> parameters, Symbols symbols,
                                  List<TermPath> out) {
        if (!(e instanceof Core.PreservedCall)) {
            TermPath here = pathOf(e, parameters, symbols);
            if (here != null) {
                if (!out.contains(here)) {
                    out.add(here);
                }
                return;   // what is under it is the same position, named once
            }
        }
        Core.forEachChild(e, child -> mentioned(child, parameters, symbols, out));
    }

    /**
     * What would have to change before this comparison could be a line.
     *
     * <p>Three different things, and a reader told one sentence for all of them cannot tell which
     * limit is theirs to wait on. A comparison between two positions asks for a class that is about
     * both, which a partition of one position is not. One on a carrier nothing draws a line on asks
     * for that carrier. What is left is a form this does not read — the position inside an
     * expression the terms do not name, or a threshold written as something other than a constant —
     * and each of the three is a different piece of work.
     */
    private static BlockReason why(Core.Binary comparison, List<String> parameters,
                                   Symbols symbols) {
        boolean leftNames = !mentionedIn(comparison.left(), parameters, symbols).isEmpty();
        boolean rightNames = !mentionedIn(comparison.right(), parameters, symbols).isEmpty();
        // Which limit stopped this is asked of what the sides name, not of how far the derivation
        // got. Two positions against each other is a rule about both of them and a class here is a
        // set of values of one — and that is as true of `x < y + 1` as of `x < y`, where reading it
        // off the derivation loses the second position entirely and answers with the carrier.
        if (leftNames && rightNames) {
            return new BlockReason.ComparisonBetweenPositions();
        }
        Core named = leftNames ? comparison.left() : comparison.right();
        if (termOf(named, parameters, symbols) == null) {
            return new BlockReason.UnreadComparisonForm();   // the position is inside something
        }
        // The carrier, asked of the carrier. `at < DateTime(...)` stops because nothing draws a line
        // on a date-time; `p.x < 1 + 2` stops because the other side is not a form a threshold is
        // read out of, and `p.x` is an `Int` — a carrier lines are drawn on all through the file.
        // Reading this off the side that did name a position calls the second one a carrier problem
        // and sends an author after a domain that is already there.
        return orderable(named.type(), symbols)
                ? new BlockReason.UnreadComparisonForm()
                : new BlockReason.UnreadComparisonDomain();
    }

    private static List<TermPath> mentionedIn(Core e, List<String> parameters, Symbols symbols) {
        List<TermPath> out = new ArrayList<>();
        mentioned(e, parameters, symbols, out);
        return out;
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
    private static List<Core> read(String behavior, Core.If iff, CoverageSites.Plan plan,
                                   List<String> parameters, Symbols symbols,
                                   List<Threshold> out, List<GuardEdge> edges,
                                   List<Guards.Singled> singled, List<BoundaryObligation> between) {
        // The comparisons a line came of, and not the positions they were about. A position carries
        // more than one statement and reading one of them settles nothing about the others.
        List<Core> made = new ArrayList<>();
        // What a row leaves behind at these comparisons, taken before any of them is read. Which
        // shape of line a comparison draws is a later question and not one this depends on — read
        // after a constant had been found, the site was a thing only a line against a constant could
        // have, and a comparison of two positions had no way to say what had reached it.
        CoverageSites.GuardRef guard = guardOf(plan, iff);
        if (guard == null) {
            return made;   // no site for this `if`: nothing could answer for it
        }
        for (Placed each : comparisonsIn(iff.cond())) {
            // The plan numbered every comparison of an instrumented condition before anything read a
            // line off one, so this is here. Required rather than looked up leniently: a line whose
            // comparison has no site is this reader and the plan disagreeing about what a condition
            // is made of.
            int site = plan.requireComparisonSiteOf(each.comparison());
            TermPath here = readOne(behavior, iff, each, plan, guard, site, parameters, symbols,
                    out, edges, singled);
            if (here != null) {
                made.add(each.comparison());
                continue;
            }
            // A line this could not read as a count of one position may still be one between two.
            // Not added to `made`: what the partition could not read here it still could not read,
            // and a boundary answering does not answer for it (spec §example-partition).
            between(behavior, iff, each, plan, guard, site, parameters, symbols, between);
        }
        return made;
    }

    /**
     * The line a comparison between two positions draws: the place where the two hold one count.
     *
     * <p>Read where a threshold could not be, and about the same comparison. A rule relating two
     * positions is not a partition of either (spec §what-a-position-admits), and that is an answer
     * about the classes rather than about the line — the row on the line is what tells a rule written
     * {@code >} from one written {@code >=}, and it is writable whenever the two positions have a
     * count they can both hold.
     *
     * <p>Asked of the carrier and not of the type. Two operands compare only when they are of one type,
     * and a type is not what makes a line measurable: an enumeration's case is comparable on its sum's
     * order while carrying no places of its own, and two newtypes of one base are two types whose
     * values are ordered alike. What both sides can be read as is the carrier, so that is what is
     * required to be one.
     *
     * <p>An equality is not one of these. {@code a == b} puts the whole of one arm on the line, and
     * that arm is already a row the branch measure asks for.
     */
    private static void between(String behavior, Core.If iff, Placed placed, CoverageSites.Plan plan,
                                CoverageSites.GuardRef guard, int site, List<String> parameters,
                                Symbols symbols, List<BoundaryObligation> out) {
        Core.Binary comparison = placed.comparison();
        if (!ordersStrictly(comparison.op())) {
            return;
        }
        NumericTerm on = termOf(comparison.left(), parameters, symbols);
        NumericTerm against = termOf(comparison.right(), parameters, symbols);
        if (on == null || against == null) {
            return;   // a position inside an expression is not a place a row can be written at
        }
        Carrier carrier = Carrier.ofValue(comparison.left().type(), symbols);
        if (carrier == null || !carrier.equals(Carrier.ofValue(comparison.right().type(), symbols))) {
            return;
        }
        // Below and inclusive are what a threshold's arms are read off, and neither is a question this
        // line answers: the two sides of it are decided by both positions at once. `singles` is false
        // because this is a line and not a value singled out, and the row that meets it is the row on
        // it.
        OriginRef.GuardOrigin origin = new OriginRef.GuardOrigin(guard, site,
                plan.site(site).obligation(), new SourceRef(guard.at().sourceId(), iff.pos()),
                true, placed.witness(), holdsAtTheLine(comparison.op()), false);
        BoundaryObligation made = new BoundaryObligation(
                new BoundaryTarget.EqualTerms(behavior, on, against, carrier), origin,
                BoundaryObligation.BoundarySide.AT);
        if (out.stream().noneMatch(had -> had.equals(made))) {
            out.add(made);
        }
    }

    /** Whether an operator orders its two sides, which {@code ==} and {@code /=} do not. */
    private static boolean ordersStrictly(Ast.BinOp op) {
        return switch (op) {
            case LT, LE, GT, GE -> true;
            case EQ, NE, AND, OR, ADD, SUB, MUL, DIV, CONCAT -> false;
        };
    }

    /** Whether the line's own values satisfy the comparison, which is what tells {@code <} from
     * {@code <=} and is the whole of what the row on the line shows. */
    private static boolean holdsAtTheLine(Ast.BinOp op) {
        return op == Ast.BinOp.LE || op == Ast.BinOp.GE;
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
     * <p>Four answers and not six, on a premise worth stating rather than leaving to be rediscovered.
     * A subtree can be forced true only where the whole condition is true and forced false only where
     * it is false — {@code &&} passes a true value down to both operands, {@code ||} passes a false
     * one, and neither passes anything the other way. So "false on {@code then}" and "true on
     * {@code else}" are unreachable and are not carried.
     *
     * <p>What makes that hold is that a condition is built from {@code &&} and {@code ||} and
     * nothing else. There is no negation operator: {@code Bool.not} is a helper, inlined to an
     * {@code if} whose condition is the comparison itself, so it never stands between a comparison
     * and the arms this is about. An operator that inverted a value inside a condition would break
     * the premise and want the other two answers, and would find this comment rather than a wrong
     * result.
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
                                    CoverageSites.Plan plan, CoverageSites.GuardRef guard, int site,
                                    List<String> parameters,
                                    Symbols symbols, List<Threshold> out, List<GuardEdge> edges,
                                    List<Guards.Singled> singled) {
        Core.Binary comparison = placed.comparison();
        Ast.BinOp op = comparison.op();
        // The carrier comes from the side that named the position, so the literal on the other side
        // is read on the carrier the line is being drawn on. A size call is an `Int` there, which is
        // the whole-number carrier, and a position holding dates is a day count — the same answer
        // `Carrier` gives everywhere else.
        NumericTerm term = termOf(comparison.left(), parameters, symbols);
        Place value = constantOf(comparison.right(),
                Carrier.ofValue(comparison.left().type(), symbols));
        if (term == null || value == null) {
            // `100000 >= cost` says what `cost <= 100000` says; read the position-bearing side first.
            term = termOf(comparison.right(), parameters, symbols);
            value = constantOf(comparison.left(),
                    Carrier.ofValue(comparison.right().type(), symbols));
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
        if (below == null) {
            // An equality singles the value out instead. Recorded as that rather than as a place to
            // cut, because the values either side of it are not a distinction the model has drawn.
            if (op != Ast.BinOp.EQ && op != Ast.BinOp.NE) {
                return null;
            }
            singled.add(new Guards.Singled(term, value,
                    new OriginRef.GuardOrigin(guard, site, plan.site(site).obligation(),
                            new SourceRef(guard.at().sourceId(), iff.pos()),
                            true, placed.witness(), op == Ast.BinOp.EQ, true)));
            return term.path();
        }
        // True at the line's own value for the operators that include it, which is not the same
        // question as which class the value falls in: `x <= c` and `x > c` agree about the second.
        boolean holds = op == Ast.BinOp.LE || op == Ast.BinOp.GE;
        out.add(new Threshold(term, value, below,
                new OriginRef.GuardOrigin(guard, site, plan.site(site).obligation(),
                        new SourceRef(guard.at().sourceId(), iff.pos()),
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
                             NumericTerm term, Place value, boolean below, boolean inclusive) {
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

    /**
     * The count a comparison is against, or null where the other side is not a value on
     * {@code carrier}.
     *
     * <p>Which count the literal is on comes from the position, not from the literal. A written
     * temporal reaches here however it is spelled, and the carrier is what says whether the days or
     * the seconds of it are the number the line is drawn at — the same question an invariant's
     * literal is asked, asked of the same place, so an invariant and a {@code guard} at one position
     * cannot admit different rules.
     */
    static Place constantOf(Core e, Carrier carrier) {
        if (carrier == null) {
            return null;
        }
        return switch (e) {
            case Core.Int i -> carrier.onTheGrid(Count.of(i.value()));
            case Core.Decimal d -> carrier.onTheGrid(Count.of(d.value()));
            case Core.Neg n -> {
                Place inner = constantOf(n.operand(), carrier);
                yield inner == null ? null : Count.number(inner).negate();
            }
            // A newtype written around a constant is that constant at this location.
            case Core.NewData nd when nd.inits().size() == 1 && nd.spreads().isEmpty() ->
                    constantOf(nd.inits().get(0).value(), carrier);
            // A temporal written the way a model writes one. Read by what the construction answers
            // with rather than by the name in front of it, so one reaches this however it is spelled.
            case Core.Call call when call.args().size() == 1
                    && call.args().get(0) instanceof Core.Str iso ->
                    (call.type() == Type.DATE && carrier instanceof Carrier.Days)
                            || (call.type() == Type.DATETIME && carrier instanceof Carrier.Seconds)
                            ? carrier.placeOf(new souther.compiler.observe.ObservedValue.Temporal(
                                    iso.value()))
                            : null;
            // A case, which is named rather than written. Where the position counts in some other
            // enumeration's declaration this is a value of neither, and the carrier says so.
            case Core.UnitValue unit -> carrier instanceof Carrier.Ordinal ordinal
                    ? ordinal.at(unit.data()) : null;
            // A string, which stands for itself. Refused where the position is not on that order,
            // so a string compared against something counted is not read as its place.
            case Core.Str str -> carrier instanceof Carrier.Text
                    ? souther.compiler.numeric.Text.of(str.value()) : null;
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

    /** Whether a line can be drawn on what this type carries, asked of the one place that says so. */
    static boolean orderable(Type type, Symbols symbols) {
        return Carrier.ofValue(type, symbols) != null;
    }

    private GuardThresholds() {}
}
