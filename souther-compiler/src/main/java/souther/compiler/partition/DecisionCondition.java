package souther.compiler.partition;

import souther.compiler.inputs.CasesLeft;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

/**
 * One distinction a body draws to decide, apart from what any path made of it.
 *
 * <p>A column of the decision the body states. What a path did with it is
 * {@link DecidedCondition}'s, and the two are apart because a rule is read both ways: a reader
 * composing a row asks what this path came out as, and a reader placing the point of a line asks
 * which rules carry <em>this</em> condition at all.
 *
 * <p><b>Not a position, and not a place.</b> Positions are a condition's operands — {@code x < y}
 * is one distinction over two of them — and where a condition is written tells one from another
 * only for as long as no two of them are written alike. So each shape below is told apart by what
 * it means, and the one shape with no meaning to be told apart by says so by being that shape.
 *
 * <p>Which is what keeps the table exclusive. Two writings of one inequality over one form are one
 * column, and a table with a column apiece for them admits an assignment where one proposition
 * holds and does not — an assignment no row can be written at and nothing can show impossible.
 */
public sealed interface DecisionCondition {

    /**
     * A comparison, in whichever vocabulary its values are compared in.
     *
     * <p>Two of them, for the reason {@link TakenConstraint} has two: the arithmetic compares a form
     * of numbers, and a position whose values count to none is compared against a written place on
     * its own order. Both are one distinction a body draws, and a reader asking which columns a rule
     * turns on asks for both — read as one shape, the second would have to be spelled as a form of
     * things that do not add.
     */
    sealed interface Comparison extends DecisionCondition {

        /** The relation this column is read as holding, which is the canonical one of the pair. */
        Rel proposition();
    }

    /**
     * A comparison the arithmetic took in, as the proposition it states.
     *
     * <p>The form and one of the two relations over it, so that a comparison and its denial are one
     * column. Which of the two is written down is settled by {@link #proposition} and is not the
     * one the author happened to write: {@code n > 100} in one body and {@code n <= 100} in another
     * are the same distinction, and a reader that took the authored side would have two columns for
     * it.
     *
     * <p>Over whichever quantities the body compared. A number of the input and a number a
     * dependency answered are compared the same way and canonicalised the same way, so
     * {@code riskScore(c) >= 700} and {@code 700 <= riskScore(c)} are one column for the reason
     * {@code n > 100} and {@code n <= 100} are.
     *
     * @param form        the comparison with its threshold moved in, so that what it states is
     *                    {@code form rel 0}
     * @param proposition the relation this column is read as holding, which is the canonical one of
     *                    the pair
     */
    record AComparison(LinearForm<DecisionAtom> form, Rel proposition)
            implements DecisionCondition.Comparison {

        public AComparison {
            if (form == null || proposition == null) {
                throw new IllegalArgumentException(
                        "a comparison of a decision is a relation over a form");
            }
            if (proposition != proposition.orItsDenial()) {
                throw new IllegalArgumentException("a comparison and its denial are one column,"
                        + " read as " + proposition.orItsDenial() + " rather than as "
                        + proposition);
            }
        }
    }

    /**
     * One position compared against a written place on the order it stands on.
     *
     * <p>The column a rule over a carrier that counts nothing draws. There is no form here because
     * there is no sum: two strings do not add, so what the body distinguished is this position
     * against this place and not a quantity against nought.
     *
     * <p>Canonicalised the same way as the one above — one of the two relations stands for the pair
     * — so that a guard and its denial are one column here as well.
     *
     * @param term the position the body compared
     * @param at   the place on its order the rule names
     */
    record AnOrderedComparison(DecisionAtom term, souther.compiler.numeric.Place at,
                               Rel proposition) implements DecisionCondition.Comparison {

        public AnOrderedComparison {
            if (term == null || at == null || proposition == null) {
                throw new IllegalArgumentException(
                        "a comparison on an order is a position, a place and a relation");
            }
            if (proposition != proposition.orItsDenial()) {
                throw new IllegalArgumentException("a comparison and its denial are one column,"
                        + " read as " + proposition.orItsDenial() + " rather than as "
                        + proposition);
            }
        }
    }

    /**
     * A value read for its truth, as the subject it is read of.
     *
     * <p>The subject and not the place. {@code guard allowed} written twice over one value is one
     * distinction, and a column apiece for them would admit an assignment where the value holds and
     * does not.
     *
     * <p>Not a comparison against {@code true}. The two answers a truth has are the two answers,
     * and saying them as a form and a relation would put a construct in the table that the body
     * never wrote — after which a reader placing the point of a line would find a line drawn on a
     * comparison nobody can be sent to.
     */
    record ATruth(DecisionSubject of) implements DecisionCondition {

        public ATruth {
            if (of == null) {
                throw new IllegalArgumentException("a truth of a decision is a truth of something");
            }
        }
    }

    /**
     * A fork on a sum, as the subject its scrutinee is.
     *
     * <p>The subject and not the arm. What a row is composed to do is put a value at a position or
     * stand a dependency in; "the second arm was taken" is a fact about the text, and a fork's arms
     * are the answers to one question about one subject rather than a question apiece.
     *
     * <p>And the answers it has, because one subject can be asked two questions. A fork on whether a
     * visit is a {@code OnceKind} or a {@code Renkei} and a fork inside the first on whether it is a
     * {@code Station} or a {@code Hospital} are both about the visit's kind, and a rule through
     * {@code Station} answers both: {@code Station} or {@code Hospital} to the first and
     * {@code Station} to the second. Told apart by the subject alone, the two would be one column
     * answered two ways, and the rule a contradiction. Two forks dividing a subject the same way
     * are one column however often a path meets them.
     *
     * <p>That the second answer implies the first is not this column's to say. Which values a row
     * may be at once is what the requirements on the way put together, and they do it by
     * intersection ({@code Requirements.merge}); a column is a question the body asked.
     *
     * @param of      the scrutinee, before any arm narrows it
     * @param answers what each arm that is a column leaves it. A set, so two forks dividing the
     *                subject alike are one question whatever order their arms are written in, and
     *                held in the one order the set makes ({@link CasesLeft#compare}) so that one
     *                question spells one way
     */
    record ACase(DecisionSubject of, Set<CasesLeft> answers) implements DecisionCondition {

        public ACase {
            if (of == null || answers == null || answers.isEmpty()) {
                throw new IllegalArgumentException(
                        "a fork of a decision is asked of something, and has answers");
            }
            Set<CasesLeft> ordered = new TreeSet<>(CasesLeft::compare);
            ordered.addAll(answers);
            answers = Collections.unmodifiableSet(ordered);
        }
    }

    /**
     * A condition read to the end that no column above is: what it states over the input, as the
     * column itself — some element of a container meeting something, several things asked at once,
     * an arm entered where a computed value is of its case.
     *
     * <p>A statement and its denial are one column, and which of the two stands for it is the one
     * whose spelling comes first ({@link #of}), so the two ways a condition comes out are the two
     * answers of one column wherever each was met.
     */
    record AStatement(Proposition statement) implements DecisionCondition {

        public AStatement {
            if (statement == null || Proposition.leavesSomethingUnread(statement)) {
                throw new IllegalArgumentException(
                        "a statement is a column where all of it was read: " + statement);
            }
            if (statement.denied().key().compareTo(statement.key()) < 0) {
                throw new IllegalArgumentException("a statement and its denial are one column,"
                        + " read as " + statement.denied().key() + " rather than as "
                        + statement.key());
            }
        }

        /** {@code stated} coming out {@code held}, as the answer to the one column it and its
         *  denial are. */
        static DecidedCondition.Held of(Proposition stated, boolean held) {
            Proposition denied = stated.denied();
            return denied.key().compareTo(stated.key()) < 0
                    ? new DecidedCondition.Held(new AStatement(denied), !held)
                    : new DecidedCondition.Held(new AStatement(stated), held);
        }
    }

    /**
     * A condition this reading has no words for, named by the reading that met it.
     *
     * <p>The one shape told apart by a name. What the other shapes carry says what they mean, and
     * two conditions nothing could read mean nothing to be told apart by — so without a name, two
     * distinctions this compiler does distinguish would be one column and the table would say a
     * body decides less than it does.
     *
     * <p>On the table rather than dropped. A rule carrying one is a rule whose conditions were not
     * all read, which is what a measurement says of itself; left off, the rule would claim to state
     * every distinction on its path.
     *
     * @param met which condition of the reading it is
     * @param whys what stopped it, in the walk's own words, each once
     */
    record AConditionNotRead(ConditionOccurrence met, List<WhyNotTaken> whys)
            implements DecisionCondition {

        public AConditionNotRead(ConditionOccurrence met, WhyNotTaken why) {
            this(met, List.of(why));
        }

        public AConditionNotRead {
            if (met == null) {
                throw new IllegalArgumentException(
                        "a condition nothing read is one some reading met, for a reason");
            }
            whys = List.copyOf(new LinkedHashSet<>(whys));
            if (whys.isEmpty()) {
                throw new IllegalArgumentException("a condition nothing read is unread for some"
                        + " reason");
            }
        }
    }
}
