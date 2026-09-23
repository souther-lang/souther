package souther.compiler.partition;

import souther.compiler.check.Comparison;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleRef;
import souther.compiler.check.StatedContract;
import souther.compiler.core.Contract;
import souther.compiler.core.Core;
import souther.compiler.diag.Citation;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.FilingCoordinate;
import souther.compiler.inputs.RulesWithNoLine;
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
 * a row cannot be written at one: what a row chooses is what the behavior is applied to. Such a
 * comparison is turned away by name rather than by drawing nothing — {@link ComparisonAssessment}
 * answers that it is about the answer, and what it raises is nothing rather than a question about
 * an input. Left to fall out as an expression this could not place, the clause was read as a rule
 * about a pair of inputs, which owes a row where the two hold one count; nothing reaches that place,
 * and the report named a rule unaccounted for that nothing could account for (issue #1013).
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
     * @param noLine  the positions a rule states something about that this drew no line at, sorted
     *                by how far the reading of each got. Carried rather than left out: a position a
     *                clause compares is not a position the model draws no line through, and a
     *                reading that answered with its lines alone would have that said of it — which
     *                is a sentence about the model, and the model says otherwise in its own
     *                declaration
     */
    public record Clauses(List<RuleEvidence> evidence,
                          List<LineDrawn> between, RulesWithNoLine noLine) {

        public static final Clauses NONE =
                new Clauses(List.of(), List.of(), RulesWithNoLine.NONE);

        public Clauses {
            evidence = List.copyOf(evidence);
            between = List.copyOf(between);
        }

        /** The lines, read off what the walk said. Not a list of their own, for the reason
         *  {@link GuardThresholds.Guards#thresholds} is not one. */
        public List<Threshold> thresholds() {
            return RuleEvidence.linesIn(evidence);
        }

        /** The values singled out, likewise. */
        public List<GuardThresholds.Guards.Singled> singled() {
            return RuleEvidence.pointsIn(evidence);
        }
    }


    /**
     * The same, reading the input's rules here.
     *
     * <p>For a caller that has no reading of them in hand. The pipeline that measures a behavior
     * reads them once and hands the same one to everything that asks, since each of these reading
     * its own is every rule of every parameter read again to arrive at the same answers.
     */
    public static Clauses of(StatedContract stated, InputDomain inputs, RuleReadingSource source) {
        return of(stated, inputs.reading(source));
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
    public static Clauses of(StatedContract stated, InputReading read) {
        if (stated == null || stated.isEmpty()) {
            return Clauses.NONE;
        }
        InputReads reads = InputReads.ofWhatIsDeclared(rootsOf(stated.params()));
        Drawn drawn = new Drawn(stated.behavior().name(), new ArrayList<>(), new ArrayList<>(),
                new RulesWithNoLine.Gathered());
        for (StatedContract.StatedRule rule : stated.rules()) {
            for (StatedContract.Conjunct conjunct : rule.conjuncts()) {
                // A conjunct this compiler could not type is one it has not read. Nothing is
                // concluded from it either way: it draws no line here, and that it drew none is not
                // a statement that the model has none there. Which part of the clause the next one
                // is does not turn on that, because a part is named by the split that made it and
                // not by how far this reading got.
                if (conjunct.stated().orNull() == null) {
                    continue;
                }
                for (ClauseStatements.Stated said : ClauseStatements.of(
                        conjunct.part(), conjunct.stated().orNull(), reads, read.symbols(),
                        read.newtypes())) {
                    switch (said.statement()) {
                        case ClauseStatements.Statement.Compares it ->
                                compared(it, rule, said.id(), read,
                                        souther.compiler.coverage.Arrivals.inTheTree(
                                                conjunct.stated().orNull()), drawn);
                        // A form no reader of clauses reads. Which positions it is about is still
                        // said, because a position left out of every answer is reported as one the
                        // model draws no line through — and the model says otherwise in the rule
                        // this stopped on. Answered here and not by whichever reader met it last:
                        // the statement is nobody's, which is one fact about it and not one per
                        // reader that turned it away.
                        case ClauseStatements.Statement.NotRead it ->
                                notRead(it, rule, read,
                                        souther.compiler.coverage.Arrivals.inTheTree(
                                                conjunct.stated().orNull()), drawn);
                        // Read by the reader that publishes what a rule tells apart
                        // ({@link BehaviorSetStatements}), and a finding here would be this reader
                        // saying it could not read a rule that was read.
                        case ClauseStatements.Statement.TellsStringsApart _ -> { }
                        case ClauseStatements.Statement.StatesNeither _ -> { }
                    }
                }
            }
        }
        return new Clauses(drawn.evidence(), drawn.between(), drawn.noLine().found());
    }

    /** What the walk has found so far, and the behavior a line between two positions is named
     *  after. Together because they are filled together and are one answer. */
    private record Drawn(String behavior, List<RuleEvidence> evidence,
                         List<LineDrawn> between,
                         RulesWithNoLine.Gathered noLine) {}

    /**
     * A statement no reader of clauses reads, at every position it is about.
     *
     * <p>The form it is written in is what stopped this — the one of the reasons that does not turn
     * on what two sides name — and the positions the statement mentions are all there is to file it
     * at. One answer at every one of them, and not a copy of a decision made elsewhere: nothing was
     * read, so no place is one the rule is known to be about the values at, and the form is what
     * each of them is left with.
     */
    private static void notRead(ClauseStatements.Statement.NotRead it,
                                StatedContract.StatedRule rule,
                                InputReading read,
                                souther.compiler.coverage.Arrivals answering, Drawn out) {
        reportRuleWithoutLine(rule.ref(), it.stated(), rule.value(),
                ComparisonAssessment.atEachOf(
                        GuardThresholds.mentionedIn(it.stated(), it.reads(), read.symbols(),
                                        read.newtypes(), answering).stream()
                                .map(FilingCoordinate::at).toList(),
                        new BlockReason.UnreadComparisonForm()),
                out.noLine());
    }

    /**
     * What one comparison a rule states comes to.
     *
     * <p>Which things a rule states, and which of them are comparisons, is
     * {@link ClauseStatements}' answer and not this reader's. Asked here, the question every reader
     * asks is "is this mine" and the only word it has for no is its own — which is how a rule read
     * as a set of strings was also reported as a comparison this could not read.
     *
     * @param said which statement of which part of the clause this one is, as the reading of what
     *             the part states issued it
     */
    private static void compared(ClauseStatements.Statement.Compares it,
                                 StatedContract.StatedRule rule, ClauseStatementId said,
                                 InputReading read,
                                 souther.compiler.coverage.Arrivals answering, Drawn out) {
        Core e = it.stated();
        InputReads reads = it.reads();
        Comparison comparison = it.comparison();
        // What the comparison comes to is read the same way wherever a comparison is written, which
        // is what {@link ComparisonAssessment} is for: a clause and a guard over one arithmetic form
        // draw one line and raise one question, and neither is worked out beside the other.
        // No arrival either: a clause stands in no body, it is checked whenever the behavior
        // answers, so there is nothing on the way to it and what arrives is the declarations'
        // whole domain — which is what an arrival that restricts nothing reads as.
        ComparisonAssessment assessed = ComparisonAssessment.of(out.behavior(), comparison.stated(),
                Citation.of(e.pos()), read,
                reads, rule.value(),
                answering, false);
        // What the positions this names are left with, where the reading of lines drew none. Asked
        // of the assessment and not worked out per arm here: the same table stood in the guard
        // reader, and a case added to an assessment had to be answered in both.
        reportRuleWithoutLine(rule.ref(), e, rule.value(),
                assessed.whatEachPlaceIsLeftWith(), out.noLine());
        // And the geometry. Read the same way a guard reads it ({@link ComparisonGeometry}); only
        // where a line's origin comes from is this reader's own — a clause's is which conjunct
        // stated it, not a place a run met.
        ComparisonGeometry geometry = ComparisonGeometry.of(assessed, cutting -> originOf(said, cutting));
        out.evidence().addAll(geometry.evidence());
        out.between().addAll(geometry.between());
    }

    /** How a row meets a line this clause drew, which is the clause's own answer and no other
     *  rule's. */
    private static LineOrigin.EnsuresOrigin originOf(ClauseStatementId said, Cutting cutting) {
        return new LineOrigin.EnsuresOrigin(new WhichLine.OfAComparisonOfAPart(said),
                new LineFacts(cutting.claim()));
    }

    /**
     * The positions a statement names that it draws no line at, for whichever of the two reasons
     * there are: this reading got partway through the rule, or it read the rule whole and there is
     * no line in it.
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
     * <p>Why there is no line is a comparison's own answer where the statement is one. Where it is
     * not — a rule stated in some other form — this reading did not take it apart at all, and the
     * form is what stopped it: the one reason that does not turn on what two sides name.
     */
    private static void reportRuleWithoutLine(RuleRef.Ensures rule, Core statement, BindingId answer,
                                     java.util.SequencedMap<FilingCoordinate,
                                             BlockReason.RuleWithoutLineReason> left,
                                     RulesWithNoLine.Gathered withoutALine) {
        if (ComparisonAssessment.readsAnswer(statement, answer)) {
            return;
        }
        souther.compiler.check.RuleCitation cited =
                new souther.compiler.check.RuleCitation.Named(rule);
        // And what each place is left with, which for a clause of an `ensures` turns on whether its
        // reading finished. Nothing works out what such a clause raises about an input — what it
        // states is a relation the behavior is held to — so where the reading stopped there is
        // nothing that was determined.
        left.forEach((named, why) -> {
            if (why instanceof BlockReason.RuleReadingStopped stopped) {
                withoutALine.unclassified(cited, named, stopped);
            } else {
                withoutALine.add(cited, named, why);
            }
        });
    }


    /**
     * Which binding names which parameter, in the tree a declaration's rules are written in.
     *
     * <p>The declaration's own bindings and not an implementation's. A rule names a parameter by the
     * binding the signature gave it, which a behavior has whether or not anything implements it —
     * so a clause of an injected behavior draws its lines like any other, and there is no body for
     * a reading to have taken them from.
     */
    static Map<BindingId, String> rootsOf(List<Contract.Param> params) {
        Map<BindingId, String> roots = new LinkedHashMap<>();
        for (Contract.Param param : params) {
            roots.putIfAbsent(param.binding(), param.name());
        }
        return roots;
    }

    private EnsuresThresholds() {}
}
