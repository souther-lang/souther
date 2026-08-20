package souther.compiler.partition;

import souther.compiler.ast.Hir;
import souther.compiler.check.BehaviorContract;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.Owed;
import souther.compiler.check.Required;
import souther.compiler.check.RuleAccounting;
import souther.compiler.check.RuleRef;
import souther.compiler.check.StatedContract;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.UnreadRule;
import souther.compiler.types.BindingId;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * The values a behavior's own {@code ensures} compares its inputs against.
 *
 * <p>A model states thresholds in more than one place. "Nothing is looked up below the first id" is
 * not in any type and is not in the body either — it is what the declaration says the behavior may
 * answer — and {@code ensures asked = NotFound -> id.value > 0} draws a line at zero as much as a
 * {@code guard} comparing the same number does.
 *
 * <p>Met by writing the value, which is where this parts from {@link GuardThresholds}, and the two
 * are not measuring the same thing. A guard's line is about control flow: the comparison is a place
 * in a body, a value can arrive at the behavior's input and never arrive there, and meeting the line
 * takes getting it to answer. A clause states a relation the behavior is held to, and its line is
 * covered by the input the relation changes at — so what meets it is a row writing that value, and
 * nothing about the run is asked. Whether some evaluation of the clause reached that conjunct is a
 * different question and not the one a boundary measures. The line still has values either side, so
 * a row is owed at the value and beside it — which is neither of the two accounts that were here
 * before, and is why the origin answers what meeting it takes rather than being read off which arm
 * it is.
 *
 * <p><b>Only what a rule requires.</b> A conjunct is part of what the rule asks of an answer, so the
 * relation changes where it does; a disjunct is not — {@code id.value > 0 || id.flagged} is
 * satisfied wherever the other side is, whatever the comparison comes to, so the relation does not
 * change at zero. Reading a line off one would put a distinction into the partition that the model
 * never drew. So the walk descends through {@code &&} and through what a {@code let} binds, which
 * is not a choice either, and stops at everything else.
 *
 * <p><b>And only about an input.</b> A comparison reading {@code value} is a line on the answer, and
 * a row cannot be written at one: what a row chooses is what the behavior is applied to. Nothing
 * turns such a comparison away — a term over the answer names no position of the input, so it draws
 * nothing, which is the same answer this gives any expression it cannot place.
 *
 * <p>Two shapes of line, the two a body's conditions draw. One at a count of a position, which
 * divides it; one between two positions, which divides neither and is on neither — asked where the
 * first came to nothing and about the same comparison, since a comparison this could not read as a
 * count of one position may still be one between two.
 */
public final class EnsuresThresholds {

    /**
     * What one reading of a behavior's declaration says about the comparisons in it.
     *
     * @param between the lines a rule draws between two of its positions, which are on neither of
     *                them and so have no axis to come off. Already obligations rather than
     *                thresholds: a line between two positions divides neither, so there is no class
     *                for a partition to be told about
     * @param unread  the positions a rule states something about that nothing here turned into a
     *                line. Carried rather than left out: a position a clause compares is not a
     *                position the model draws no line through, and a reading that answered with its
     *                lines alone would have that said of it — which is a sentence about the model,
     *                and the model says otherwise in its own declaration
     */
    public record Clauses(List<Threshold> thresholds, List<GuardThresholds.Guards.Singled> singled,
                          List<LineDrawn> between, List<UnreadRule> unread,
                          List<GuardThresholds.Guards.AtAPosition> accounting) {

        public static final Clauses NONE =
                new Clauses(List.of(), List.of(), List.of(), List.of(), List.of());

        public Clauses {
            thresholds = List.copyOf(thresholds);
            singled = List.copyOf(singled);
            between = List.copyOf(between);
            unread = List.copyOf(unread);
            accounting = List.copyOf(accounting);
        }
    }

    /**
     * The lines one behavior's clauses draw.
     *
     * <p>Read in the representation the declaration's own rules are held in, which keeps the
     * operations the language defines the meaning of standing. That is what the rules were read into
     * once ({@link StatedContract}); a second reading of them would be a second chance to disagree
     * with what a caller is told it may assume.
     *
     * @param stated the behavior's rules, or null where it declares none or its declaration could
     *               not be read. Both leave nothing to draw a line from, and which of them happened
     *               is said where the declaration is held to its rules
     */
    public static Clauses of(StatedContract stated, InputDomain inputs, Symbols symbols) {
        if (stated == null || stated.isEmpty()) {
            return Clauses.NONE;
        }
        InputReads reads = InputReads.ofWhatIsDeclared(inputs, rootsOf(stated.params()));
        Drawn drawn = new Drawn(stated.behavior().name(), new ArrayList<>(), new ArrayList<>(),
                new ArrayList<>(), new ArrayList<>(), new ArrayList<>());
        for (StatedContract.StatedRule rule : stated.rules()) {
            String clause = labelOf(rule);
            for (StatedContract.Conjunct conjunct : rule.conjuncts()) {
                // A conjunct this compiler could not type is one it has not read. Nothing is
                // concluded from it either way: it draws no line here, and that it drew none is not
                // a statement that the model has none there.
                if (conjunct.stated() != null) {
                    stated(conjunct.stated(), rule, clause, reads, symbols, drawn);
                }
            }
        }
        return new Clauses(drawn.thresholds(), drawn.singled(), drawn.between(), drawn.unread(),
                drawn.accounting());
    }

    /** What the walk has found so far, and the behavior a line between two positions is named
     *  after. Together because they are filled together and are one answer. */
    private record Drawn(String behavior, List<Threshold> thresholds,
                         List<GuardThresholds.Guards.Singled> singled,
                         List<LineDrawn> between, List<UnreadRule> unread,
                         List<GuardThresholds.Guards.AtAPosition> accounting) {}

    /**
     * The comparisons a rule states outright: its own, and those of both sides of every {@code &&}
     * above them.
     *
     * <p>Nothing below anything else. A disjunct holds where the other one does not, a call's
     * argument is not what the call comes to, and neither states the comparison inside it — so a
     * line drawn from one would be a line the model does not draw.
     */
    private static void stated(Core e, StatedContract.StatedRule rule, String clause,
                               InputReads reads, Symbols symbols, Drawn out) {
        if (e instanceof Core.Binary both && both.op() == Hir.BinOp.AND) {
            stated(both.left(), rule, clause, reads, symbols, out);
            stated(both.right(), rule, clause, reads, symbols, out);
            return;
        }
        // Through what a `let` binds, which is not a choice: what the expression comes to is its
        // body, so the body states whatever the rule states. This is the shape a helper called from
        // a clause arrives in — the call is expanded and its argument bound to the helper's own
        // parameter — and a walk that stopped here found the rule stating nothing while the model
        // plainly says something about the position.
        if (e instanceof Core.LetIn let) {
            stated(let.body(), rule, clause, reads.and(let.binder(), let.value()), symbols, out);
            return;
        }
        // A disjunction was read, and what it states is not what either side of it states. Said as
        // nothing rather than as a rule this could not read: reporting it would send an author after
        // a limit of this compiler that is not there.
        if (e instanceof Core.Binary or && or.op() == Hir.BinOp.OR) {
            return;
        }
        // Anything else is a form this walk does not read. Which positions it is about is still
        // said, because a position left out of every answer is reported as one the model draws no
        // line through — and the model says otherwise in the rule this stopped on.
        if (!(e instanceof Core.Binary comparison) || !GuardThresholds.orders(comparison.op())) {
            reportUnread(new RuleRef.Ensures(rule.id(), clause), e, rule.value(),
                    reads, symbols, out.unread());
            return;
        }
        // What the comparison cuts is read the same way wherever a comparison is written, which is
        // what {@link Cutting} is for: a clause and a guard over one arithmetic form draw one line,
        // and a reader that called two of the three readings read no form at all.
        Cutting cutting = Cutting.of(out.behavior(), comparison, reads, symbols);
        if (cutting == null) {
            // The positions are named as unread, because what the partition could not read here it
            // still could not read.
            reportUnread(new RuleRef.Ensures(rule.id(), clause), comparison,
                    rule.value(), reads, symbols, out.unread());
            // Every position the comparison names, by the walk a body's conditions use. Asked of the
            // narrower reading instead, a comparison this could not read had no position to be filed
            // at — which is exactly the comparison whose questions stand, so the clause that most
            // needs saying said nothing.
            List<TermPath> named = GuardThresholds.mentionedIn(comparison, reads, symbols);
            raises(out, rule, clause, comparison, rule.value(),
                    named.isEmpty() ? null : named.get(0),
                    GuardThresholds.comparedTerm(comparison, reads, symbols),
                    GuardThresholds.subjectsOf(comparison, reads, symbols, rule.value()),
                    new Required.LineRead.NoLine(
                            GuardThresholds.why(comparison, reads, symbols)));
            return;
        }
        OriginRef.EnsuresOrigin origin = new OriginRef.EnsuresOrigin(
                new RuleRef.Ensures(rule.id(), clause), cutting.valueBelongsBelow(),
                cutting.holdsAtTheValue(), cutting.singles());
        NumericTerm divided = cutting.dividedPosition();
        if (divided == null) {
            // A line on something that is not one position's own values: it divides no position, so
            // it travels beside the partition rather than on an axis. Met by writing the values,
            // which is this reader's own answer and not the one the same shape of line gets from a
            // guard — a guard's is met by getting the comparison to answer, because what it is about
            // is a place in a body.
            // The positions are named as ones nothing divides, which is what a rule over a quantity
            // that is not one position's own values leaves them — the same note the same shape gets
            // from a body's conditions, said by the same reader.
            reportUnread(new RuleRef.Ensures(rule.id(), clause), comparison,
                    rule.value(), reads, symbols, out.unread());
            // Null where the quantity does not reach the line, which is the line and not one of its
            // points. What a clause raises is answered by what came of reading it and never by which
            // reading was tried: read off the branch, a rule that drew nothing reported a line.
            // Collected rather than turned into a border here, for the reason a body's lines are:
            // what a border owes away from its line is a run of the arrangement every rule about
            // that quantity makes together.
            boolean made = Border.reaches(cutting.target(), cutting.within());
            if (made) {
                out.between().add(new LineDrawn(cutting, origin));
            }
            List<TermPath> named = GuardThresholds.mentionedIn(comparison, reads, symbols);
            raises(out, rule, clause, comparison, rule.value(),
                    named.isEmpty() ? null : named.get(0),
                    GuardThresholds.comparedTerm(comparison, reads, symbols),
                    GuardThresholds.subjectsOf(comparison, reads, symbols, rule.value()),
                    made ? new Required.LineRead.ALineBetweenTwoPositions()
                            : new Required.LineRead.NoLine(
                                    GuardThresholds.why(comparison, reads, symbols)));
            return;
        }
        raises(out, rule, clause, comparison, rule.value(), divided.path(), divided,
                GuardThresholds.subjectsOf(comparison, reads, symbols, rule.value()),
                new Required.LineRead.ALineOnThePosition());
        // And the line itself, where the position has no value beside it for a row to be owed at,
        // for the reason a body's line is: the classes either side are what the model tells apart,
        // and the border is drawn on the quantity the rule wrote, which can name where it falls.
        if (cutting.dividedValue() == null
                && Border.reaches(cutting.target(), cutting.within())) {
            out.between().add(new LineDrawn(cutting, origin));
        }
        // The value the classes meet at, which the reading of the comparison already
        // answered. Taken off the level the rule was written with, a rule that wrote a
        // multiple of the position named a class at a number the position never holds.
        souther.compiler.numeric.Place value = cutting.dividedValue();
        if (cutting.singles()) {
            // The value the rule names, for the reason a body's rule gets: where its line falls and
            // not the value beside it.
            souther.compiler.numeric.Place names = cutting.singledValue();
            if (names != null) {
                out.singled().add(new GuardThresholds.Guards.Singled(divided, names, origin));
            }
        } else {
            out.thresholds().add(
                    new Threshold(divided, cutting.seam(), cutting.valueBelongsBelow(), origin));
        }
    }

    /**
     * What one clause's comparison raises, and what the reading of it answered.
     *
     * <p>Off the comparison and not off the lines that came back, for the reason a body's is: a
     * comparison states where the values stop by being written that way, and one this could not
     * read is exactly where nothing answers it.
     */
    private static void raises(Drawn out, StatedContract.StatedRule rule, String clause,
                               Core.Binary comparison, BindingId answer, TermPath at,
                               NumericTerm term,
                               Required.ComparisonSubject of, Required.LineRead read) {
        if (at == null) {
            return;   // about no position of the input, so it raises nothing about one
        }
        RuleRef.Ensures named = new RuleRef.Ensures(rule.id(), clause);
        out.accounting().add(new GuardThresholds.Guards.AtAPosition(at, term,
                RuleAccounting.ofComparison(named, ComparisonClaim.of(comparison.op()), of, read,
                        // A clause belongs to a behavior, so there is always something to call it.
                        souther.compiler.check.RuleCitation.named(named))));
    }

    /**
     * The positions a statement names that nothing turned into a line, where that is a limit of
     * this compiler.
     *
     * <p>Named rather than passed over, because a position left out of every answer is reported as
     * one the model draws no line through — a sentence about the model, and the model says otherwise
     * in the clause two tokens away. Asked of the statement and not of the positions: a position
     * carries more than one statement, and a line read at it settles nothing about the rest.
     *
     * <p><b>Except where the other side is the answer.</b> {@code value.sku == item.sku} was read,
     * and understood, and draws no line a row can be written at — what a row chooses is what the
     * behavior is applied to. Reported as unread it sends an author after a limit of this compiler
     * that is not there, which is the opposite mistake to the one above and just as wrong.
     *
     * <p>Why it could not be read is a comparison's own answer where the statement is one. Where it
     * is not — a rule stated in some other form — what stopped this is the form, which is the one
     * of the three reasons that does not turn on what two sides name.
     */
    private static void reportUnread(RuleRef.Ensures rule, Core statement, BindingId answer,
                                     InputReads reads, Symbols symbols, List<UnreadRule> unread) {
        if (readsTheAnswer(statement, answer)) {
            return;
        }
        BlockReason.AboutARule why = statement instanceof Core.Binary comparison
                ? GuardThresholds.why(comparison, reads, symbols)
                : new BlockReason.UnreadComparisonForm();
        souther.compiler.check.RuleCitation cited =
                souther.compiler.check.RuleCitation.named(rule);
        for (TermPath named : GuardThresholds.mentionedIn(statement, reads, symbols)) {
            UnreadRule here = new UnreadRule(rule, cited, named, why);
            if (unread.stream().noneMatch(had -> had.sameAs(here))) {
                unread.add(here);
            }
        }
    }

    /** Whether anything in {@code e} reads what the rule calls the answer. */
    private static boolean readsTheAnswer(Core e, BindingId answer) {
        if (e instanceof Core.Read read && read.binding() != null
                && read.binding().equals(answer)) {
            return true;
        }
        boolean[] found = {false};
        Core.forEachChild(e, child -> found[0] |= readsTheAnswer(child, answer));
        return found[0];
    }

    /**
     * What a report calls one rule of a clause.
     *
     * <p>The author's name for the clause where they gave one, since that is what they will look
     * for. Where they did not, the case the arm is about, which is the other thing written next to
     * the rule. A clause over an answer with no cases has neither, and the behavior's own name is
     * then the whole of what there is to say.
     */
    private static String labelOf(StatedContract.StatedRule rule) {
        if (rule.clause().isPresent()) {
            return rule.clause().get();
        }
        return rule.id().selector() == null ? "" : rule.id().selector().name();
    }

    /**
     * Which binding names which parameter, in the tree a declaration's rules are written in.
     *
     * <p>The declaration's own bindings and not an implementation's. A rule names a parameter by the
     * binding the signature gave it, which a behavior has whether or not anything implements it —
     * so a clause of an injected behavior draws its lines like any other, and there is no body for
     * a reading to have taken them from.
     */
    private static Map<BindingId, String> rootsOf(List<BehaviorContract.ContractParam> params) {
        Map<BindingId, String> roots = new LinkedHashMap<>();
        for (BehaviorContract.ContractParam param : params) {
            roots.putIfAbsent(param.binding(), param.name());
        }
        return roots;
    }

    private EnsuresThresholds() {}
}
