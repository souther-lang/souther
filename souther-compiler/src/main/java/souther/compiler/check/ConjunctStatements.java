package souther.compiler.check;

import souther.compiler.semantics.ConditionJoin;

import java.util.ArrayList;
import java.util.List;

/**
 * The statements one conjunct of a clause states, numbered where they are recognised.
 *
 * <p>What a conjunct states is more than one thing wherever a denial was carried into a choice or a
 * helper's body joined two rules, and each of them is a statement of the model in its own right
 * ({@link InvariantStatementId}). Which of the conjunct's statements a reader is holding is the one
 * thing that tells them apart, so the number is issued here and nowhere else: a second walk with a
 * counter of its own numbers the same rule differently the day the two disagree about what a
 * conjunct states, and a reading that made less of a clause would issue numbers a reading that made
 * more of it never reaches.
 *
 * <p>The walk is the shape's and recognises no connective of its own. A binding is crossed, a
 * conjunction is descended into, and what is left is a statement — which is what {@link ClauseExpr}
 * already decided when it read the clause's connectives once.
 */
final class ConjunctStatements {

    private ConjunctStatements() {
    }

    /**
     * One statement of a conjunct: which it is, what it says, and the bindings a reading crossed to
     * reach it.
     *
     * <p>The bindings are handed over rather than applied, because what a reading does on crossing
     * one is its own: a reading that carries an environment enters each of them, and one that reads
     * only what the statement compares has nothing to enter. Applied here, this would be the walk
     * deciding what crossing a binding means for readers that have not been written.
     *
     * @param statement which statement of which conjunct it is
     * @param said      the part the reading arrived at, with the denials above it already spent
     * @param crossed   the bindings standing between the conjunct and this statement, outermost
     *                  first
     */
    record Reached(InvariantStatementId statement, ClauseExpr.Part said,
                   List<ClauseExpr.Scoped> crossed) {

        Reached {
            if (statement == null || said == null) {
                throw new IllegalArgumentException(
                        "a statement of a conjunct is some statement, and says something");
            }
            crossed = List.copyOf(crossed);
        }
    }

    /**
     * One statement of a conjunct before it is numbered: what it says, and the bindings a reading
     * crossed to reach it.
     *
     * <p>For a reader that asks what a clause states and does not file the answer under a rule's
     * part, which is the only thing a number is for.
     */
    record Stated(ClauseExpr.Part said, List<ClauseExpr.Scoped> crossed) {

        Stated {
            if (said == null) {
                throw new IllegalArgumentException("a statement of a conjunct says something");
            }
            crossed = List.copyOf(crossed);
        }
    }

    /**
     * Every statement {@code part} states, in the order a reading arrives at them, each with the
     * number the part was handed for it or, where it was handed none, the next number of its
     * conjunct.
     */
    static List<Reached> of(Clauses.StatedPart part) {
        List<Stated> stated = statedBy(part.of());
        List<Reached> out = new ArrayList<>();
        // Numbered here, before anything is made of it. Numbered where an end or a hand-over is
        // written down instead, the number would say which of the outcomes this was rather than
        // which of the statements.
        if (!part.statements().isEmpty() && part.statements().size() != stated.size()) {
            throw new IllegalStateException(part.id() + " states " + stated.size()
                    + " statements here and was handed the numbers of " + part.statements().size());
        }
        for (int each = 0; each < stated.size(); each++) {
            out.add(new Reached(numberedAs(part, each), stated.get(each).said(),
                    stated.get(each).crossed()));
        }
        return List.copyOf(out);
    }

    /**
     * The identity of statement {@code index} of {@code part}: the number the part was handed for
     * it, or the next number of its conjunct.
     *
     * <p>The one place a statement is given its identity, for the reading that reads a part and for
     * the one that finds what it states of every element. Two places each choosing between the
     * number handed and the next one are two answers to which statement this is, and the second of
     * them is the one a statement inside a statement inside a conjunct is asked of.
     */
    static InvariantStatementId numberedAs(Clauses.StatedPart part, int index) {
        return new InvariantStatementId(part.id(), part.statements().isEmpty()
                ? StatementNumber.of(index) : part.statements().get(index));
    }

    /**
     * Every statement {@code conjunct} states, in the order a reading arrives at them, as they are
     * before they are numbered. The same walk {@link #of} numbers, so the two cannot disagree about
     * what a conjunct states.
     */
    static List<Stated> statedBy(ClauseExpr conjunct) {
        List<Stated> out = new ArrayList<>();
        reach(conjunct, List.of(), out);
        return List.copyOf(out);
    }

    private static void reach(ClauseExpr saidAs, List<ClauseExpr.Scoped> crossed,
                              List<Stated> out) {
        // A binding, which is where the environment a reading carries changes and the one shape
        // that is not a part. Whether a denial stands above it decides nothing: the denial is
        // carried to the leaves as the clause is read, so the body under a binding already states
        // what the binding states.
        if (saidAs instanceof ClauseExpr.Scoped scoped) {
            List<ClauseExpr.Scoped> inside = new ArrayList<>(crossed);
            inside.add(scoped);
            reach(scoped.body(), inside, out);
            return;
        }
        // What one part states may be more than one rule: a part that names a rule is that rule's
        // body written here, and a body joining two of them states both.
        //
        // Asked of what the connective composes alone. How the whole of it stands is a separate
        // answer and is already inside this one — the denial a clause was read under is applied to
        // what the connective composes where the shape is made, so a choice denied arrives saying
        // it composes both. Asked together with how the whole stands, the denial is applied a
        // second time and a conjunction an author wrote as a denied choice is never descended into.
        if (saidAs instanceof ClauseExpr.Joined joined && joined.how() == ConditionJoin.BOTH) {
            reach(joined.left(), crossed, out);
            reach(joined.right(), crossed, out);
            return;
        }
        // A binding is crossed above and a conjunction is descended into, so what is left is a part
        // of the clause: a leaf, or a choice a reading takes whole.
        out.add(new Stated((ClauseExpr.Part) saidAs, crossed));
    }
}
