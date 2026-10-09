package souther.compiler.partition;

import souther.compiler.check.AffineForms;
import souther.compiler.check.BooleanMeaning;
import souther.compiler.check.DeclaredArgument;
import souther.compiler.check.Comparison;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.Location;
import souther.compiler.check.DeclarationAccess;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.StatedComparison;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputNumber;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.PathResolution;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * A comparison over what a dependency answered, as the proposition it states.
 *
 * <p>What {@link AffineReading} is for the input, over the quantities a row can control rather than
 * the ones it writes. The arithmetic is the same walk — {@link AffineForms} takes what an atom is
 * from whoever asks — so {@code riskScore(c).value + 10 >= 710} and {@code riskScore(c).value >=
 * 700} are one proposition here for the reason they are one over a position.
 *
 * <p><b>Asked only where the input's arithmetic read nothing.</b> The two vocabularies do not
 * overlap: a comparison every operand of which is a number of the input is read there and a line is
 * drawn on it, and one this answers names at least one answer, which no term of the input is. So a
 * comparison is read once, and a column of the table and a border on the same comparison cannot
 * come from two readings that disagree.
 *
 * <p>And a {@code Bool} answer held against a truth the source settles is that answer's truth:
 * {@code known(name) == false} holding is {@code known(name)} not holding, and one column, which is
 * what {@link souther.compiler.inputs.InputTruth} makes of the same spelling over a position.
 */
record DecisionComparison(InputDomain inputs, RuleReadingSource rules, DecisionSubjects subjects) {

    /**
     * {@code comparison} coming out {@code held} as a column, or null where nothing here reads it.
     *
     * <p>Null where an operand is neither a number of the input nor a place inside an answer, and
     * null where every operand is a number of the input: that comparison is the arithmetic's to
     * read, and answering it here would be a second reading of it.
     */
    DecidedCondition of(Comparison comparison, InputReads reads, boolean held) {
        DecidedCondition truth = truthOfAnAnswer(comparison.stated(), reads, held);
        if (truth != null) {
            return truth;
        }
        LinearForm<DecisionAtom> whole = overAnAnswer(comparison.stated(), reads);
        return whole == null ? null : stated(whole, comparison.stated().claim(), held);
    }

    /**
     * Whether {@code comparison} is a column here: a proposition over what a dependency answered.
     *
     * <p>The question a reading of the input asks before it says it could not read the comparison.
     * Such a comparison is about a value a row stands in rather than writes, and this reading names
     * it; answered by the reading of the input on its own, the column the table holds would be
     * reported beside it as a rule nobody read.
     */
    boolean readsOverAnAnswer(StatedComparison comparison, InputReads reads) {
        return truthOfAnAnswer(comparison, reads, true) != null
                || overAnAnswer(comparison, reads) != null;
    }

    /**
     * {@code comparison} coming out {@code held} as the truth of a {@code Bool} answer, or null where
     * it does not hold one against a truth the source settles.
     */
    private DecidedCondition truthOfAnAnswer(StatedComparison comparison, InputReads reads,
                                             boolean held) {
        return BooleanMeaning.againstATruth(comparison, held, rules.symbols(),
                        side -> subjects.isTheTruthOfAnAnswer(side, reads))
                .map(against -> (DecidedCondition) subjects.truthOf(against.side(),
                        against.held(), reads))
                .orElse(null);
    }

    /** The quantity {@code comparison} states, or null where it is not one over an answer. */
    private LinearForm<DecisionAtom> overAnAnswer(StatedComparison comparison, InputReads reads) {
        LinearForm<DecisionAtom> left = null;
        for (Core side : List.of(comparison.left(), comparison.right())) {
            if (!(AffineForms.outcome(side, reads, reading())
                    instanceof AffineForms.Outcome.Composed<DecisionAtom, InputReads>(
                            LinearForm<DecisionAtom> form))) {
                return null;
            }
            if (left == null) {
                left = form;
                continue;
            }
            // A difference no ratio holds is a comparison that is not read as a decision, the same
            // as a side that is no form.
            LinearForm<DecisionAtom> whole = left.minus(form).orNull();
            if (whole == null || whole.coefs().isEmpty()
                    || whole.coefs().keySet().stream()
                            .noneMatch(DecisionAtom.OfAnAnswer.class::isInstance)) {
                return null;
            }
            return whole;
        }
        throw new IllegalStateException("a comparison has two sides");
    }

    /**
     * The column {@code whole} states, facing the one way this reading writes it.
     *
     * <p><b>Which way is a fact about the proposition and not about the source.</b> A line keeps
     * the quantity its author put on the left, because a report sends a reader to the comparison
     * they wrote; a column is shown to nobody — what a sentence points at is the construct — and
     * what it has to do is come out the same for two bodies that state one thing. Read off the
     * authored side, {@code a >= b} and {@code b <= a} are two columns over quantities that are
     * each other negated, and a table with both admits an assignment where one proposition holds
     * and does not.
     *
     * <p>So the quantity is written the one way every writing of a relation comes to ({@link
     * Relation.OneWay}), which is the way the reading of what a condition means writes it too.
     */
    private DecidedCondition stated(LinearForm<DecisionAtom> whole, ComparisonClaim written,
                                    boolean held) {
        Rel states = written.statedRelation();
        Relation.OneWay<DecisionAtom> one =
                Relation.OneWay.of(whole, held ? states : states.denied());
        return new DecidedCondition.Compared(
                new DecisionCondition.AComparison(one.form(), one.proposition()), one.holds());
    }

    /**
     * How a side of the comparison is read.
     *
     * <p>Everything but the leaf is the reading the input's arithmetic uses, asked of the same
     * answers: what a name denotes and what a field access reads through are facts about the body,
     * and a second answer to either would be this reading disagreeing with the one a line is drawn
     * with about a body they are both reading.
     */
    private AffineForms.Reading<DecisionAtom, InputReads> reading() {
        return new AffineForms.Reading<DecisionAtom, InputReads>() {

            @Override
            public Symbols symbols() {
                return rules.symbols();
            }

            @Override
            public DeclarationAccess declarations() {
                return rules.declarations();
            }

            @Override
            public LinearForm<DecisionAtom> leafOf(Core node, InputReads at) {
                NumericTerm term = InputNumber.of(node, inputs, at, rules);
                DecisionAtom atom = term != null ? new DecisionAtom.OfTheInput(term)
                        : subjects.of(node, at) instanceof DecisionSubject.AnAnswer answered
                                ? new DecisionAtom.OfAnAnswer(answered) : null;
                return atom == null ? null : LinearForm.atom(atom);
            }

            @Override
            public InputReads inside(Core.LetIn li, InputReads at) {
                return at.and(li.binder(), li.value());
            }

            @Override
            public AffineForms.ReadThrough<InputReads> readThrough(Core.Read read, InputReads at) {
                return NameAnswers.denoting(read, at, rules.symbols(), rules.newtypes());
            }

            @Override
            public List<AffineForms.ReadThrough<InputReads>> alternativesOf(Core.Read read,
                                                                           InputReads at) {
                return NameAnswers.alternativesOf(read, at, rules.symbols(), rules.newtypes());
            }

            @Override
            public AffineForms.ReadThrough<InputReads> taken(Core node, InputReads at) {
                return NameAnswers.taken(node, at);
            }

            @Override
            public LinearForm<DeclaredArgument> takenAsAForm(Core node, InputReads at) {
                return NameAnswers.takenAsAForm(node, at);
            }

            @Override
            public boolean readsThrough(Core.FieldAccess fa, InputReads at) {
                boolean stands = switch (at.pathOf(fa.target(), rules.newtypes())) {
                    case PathResolution.At _ -> true;
                    case PathResolution.NotAPosition _ -> false;
                    case PathResolution.MayStandAt _ -> true;
                };
                return !stands
                        && !Location.isStep(fa.target().type(), fa.field(), rules.newtypes());
            }
        };
    }

    /** The atoms of a form, wrapped as the input's, which is what a comparison the arithmetic read
     *  states here. */
    static LinearForm<DecisionAtom> ofTheInput(LinearForm<NumericTerm> form) {
        Map<DecisionAtom, ExactRatio> coefs = new LinkedHashMap<>();
        form.coefs().forEach((term, coefficient) ->
                coefs.put(new DecisionAtom.OfTheInput(term), coefficient));
        return new LinearForm<>(form.constant(), coefs);
    }
}
