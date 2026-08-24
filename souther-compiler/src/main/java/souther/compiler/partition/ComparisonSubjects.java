package souther.compiler.partition;

import souther.compiler.check.Owed;
import souther.compiler.check.Required;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.diag.Citation;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.types.BindingId;

/**
 * What a comparison is a rule about, which the operator does not say.
 *
 * <p>The operator says what a comparison places — {@code x == 10} singles a value out and
 * {@code x < 10} orders the values either side — and this says what it places it about. Neither is
 * the other's, and taken from the operator alone {@code a == b} raised a question about a value
 * singled out at {@code a} that no rule wrote.
 *
 * <p><b>Boundary coverage is over the values a row can choose, which are the behavior's inputs.</b>
 * A comparison involving the answer may state a relation between an input and the answer, and this
 * reading does not project that relation back onto the input space. Such a comparison is read and
 * understood, and it raises no input-coverage obligation.
 *
 * <p><b>Two axes, and they were one.</b> Whether a side reads the answer and whether a side names
 * an input position were asked as one question — "does this move with the row" — and both come back
 * true, because the answer does move with the row. That much is a fact. What did not follow is that
 * two things moving with the row are the same kind of subject on the input space: an order between
 * two inputs is a line rows are owed at, and an order between an input and the answer is not a line
 * at all. Read as one, {@code List.length(value.articles) <= query.limit.value} raised a boundary
 * obligation at a place the reading of the clause can never reach, and the report said a rule went
 * unaccounted for that nothing could ever account for (issue #1013).
 *
 * <p><b>Not a claim that no line exists.</b> Eliminating the answer existentially can leave a
 * constraint on the input — {@code List.length(value.items) <= n} has no satisfying answer where
 * {@code n} is negative, because a length is never negative — and deriving that is constraint
 * projection rather than the reading of one comparison. What is written here is where this reading
 * stops, so that adding the projection later does not contradict it.
 */
final class ComparisonSubjects {

    /**
     * What {@code comparison} is a rule about.
     *
     * <p>The one way in, and the only thing here that classifies anything. {@code answer} is the
     * binding a clause calls what the behavior answers, or null where the comparison is written in
     * a body and there is nothing to be the answer.
     */
    static Required.ComparisonSubject of(Core.Binary comparison, InputReads reads, Symbols symbols,
                                         BindingId answer) {
        // Asked first, and of the whole comparison. A rule that reads the answer anywhere in it is
        // one this reading does not put on the input space, whichever side the answer is on and
        // whatever else stands beside it: `value.n + query.offset <= 20` is about the answer and
        // about an input, and the input is no more measurable here for the input being named.
        if (readsAnswer(comparison, answer)) {
            return new Required.ComparisonSubject.AnswerDependent();
        }
        boolean left = mentionsAnInput(comparison.left(), reads, symbols);
        boolean right = mentionsAnInput(comparison.right(), reads, symbols);
        if (left == right) {
            // Both, which is a rule about a pair; or neither, which says nothing about an input.
            // The place a relation's line falls is between the two sides, spelled as they are
            // written — a reader meets them beside each other on the row owed there.
            return left ? new Required.ComparisonSubject.Relation(
                    new Owed.Subject.OfComparison(Citation.of(comparison.pos())))
                    : new Required.ComparisonSubject.NoInput();
        }
        Core side = left ? comparison.left() : comparison.right();
        NumericTerm term = GuardThresholds.termOf(side, reads, symbols);
        if (term == null) {
            // An input read a way the terms do not name. `NoInput` understates this — see the arm's
            // own note and issue #1029 — and no arm of this classification says it better today.
            return new Required.ComparisonSubject.NoInput();
        }
        return new Required.ComparisonSubject.AnInput(subjectOf(term), Owed.Subject.at(""));
    }

    /**
     * Whether anything in {@code e} reads the binding a rule calls the answer.
     *
     * <p>A mechanical predicate over the tree, and it classifies nothing by itself. Two readers ask
     * it and reach different conclusions: {@link #of} answers that the comparison raises no
     * input-coverage obligation, and {@link EnsuresThresholds} answers that a rule about the answer
     * is not one this compiler failed to read. Written twice, the two came apart — the second had
     * the predicate and the first did not, which is the whole of issue #1013 — so it is written
     * once and neither reader owns what the other makes of it.
     *
     * <p>Syntactic. {@code value.n - value.n + query.limit.value <= 20} does not depend on the
     * answer once the arithmetic is read, and this answers that it does. Normalising first is a
     * larger question about which reading of a comparison decides its subject (#1029), and a
     * predicate that quietly did some of it would put that decision here.
     *
     * <p>False where there is no answer to read, which is every comparison written in a body.
     */
    static boolean readsAnswer(Core e, BindingId answer) {
        if (answer == null) {
            return false;
        }
        if (e instanceof Core.Read read && answer.equals(read.binding())) {
            return true;
        }
        boolean[] found = {false};
        Core.forEachChild(e, child -> found[0] |= readsAnswer(child, answer));
        return found[0];
    }

    /**
     * Whether {@code e} names a position of the behavior's input.
     *
     * <p>By the walk that names positions however they are written, which is the reading a body's
     * conditions use. What it does not say is whether the position is one a line can be drawn on:
     * a side may name an input and still have no term this reading can measure it by.
     */
    private static boolean mentionsAnInput(Core e, InputReads reads, Symbols symbols) {
        return !GuardThresholds.mentionedIn(e, reads, symbols).isEmpty();
    }

    /**
     * What the question is about, relative to the position it is filed at.
     *
     * <p>An invariant's subject is relative to the value its clause is on, and this is the same
     * thing one frame out. Which of the two it is was settled by the reading that found the term: a
     * {@code String} bounded on its length raises about the string and draws its line on the count,
     * and a document promises both spellings.
     */
    private static Owed.Subject.OfAPosition subjectOf(NumericTerm term) {
        // A term that is what an operation answered says the line is on that answer; a term over the
        // position's own value, or no term at all, leaves it on the position. Which operation it was
        // makes no difference here — the line under `Int.abs(x) > 10` is no more on `x` than the one
        // under `String.length(s) > 10` is on `s` — so this is the one question the variant is
        // genuinely what settles.
        return new Owed.Subject.OfAPosition("", term instanceof NumericTerm.TakenOf);
    }

    private ComparisonSubjects() {}
}
