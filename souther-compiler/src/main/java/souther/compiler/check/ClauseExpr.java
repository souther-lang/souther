package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.semantics.ConditionJoin;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * A clause as its connectives, read out of the tree once.
 *
 * <p>What a clause is written out of — a conjunction, a choice, a denial — is the clause's own
 * shape. It used to be read by each reading that wanted it, which was one mapping from {@link Core}
 * per reading and as many chances for them to drift; and it had to be read again by anything that
 * wanted to look at the clause before answering it, which is how a walk that decided what a reading
 * could afford came to interpret {@code &&} a second time.
 *
 * <p>So the shape is read here and nowhere else. What comes out is this, and everything downstream
 * — what the values leave, where the ends are, what has to be built and what it costs — is an
 * evaluator over it. Two evaluators over one structure are not two readings of one clause: they
 * agree about what the clause is by construction, because neither of them is the thing that decided.
 *
 * <p><b>Denials are gone by the time this exists.</b> A denial is carried to the leaves as the tree
 * is read, so a conjunction denied is the choice between its parts denied, and a leaf says which of
 * the two it states. What is left holds no {@code not}, and a reader below never has to ask whether
 * it is inside one.
 *
 * <p><b>The tree's own nodes are kept.</b> A reader that walks the clause afterwards looks up what
 * this made of the very node it is holding, so every node that mapped to a shape is written down —
 * a denial and what is under it map to the same shape and both are named. Shapes are not gathered
 * across brackets for the same reason: {@code (a && b) && c} holds a node for {@code a && b}, and a
 * reader asking about it is asking about something the author wrote.
 */
sealed interface ClauseExpr {

    /**
     * The tree nodes this stands for, outermost first.
     *
     * <p>More than one where a denial was carried down: {@code not(x)} and {@code x} are one shape
     * and two nodes, and a reader holding either of them is holding this.
     */
    List<Core> spelled();

    /** One part of no connective, stated where {@code positive} and denied where it is not. */
    record Leaf(List<Core> spelled, boolean positive) implements ClauseExpr {

        public Leaf {
            spelled = named(spelled);
        }

        /** The part itself, which is the innermost of what it is spelled as. */
        Core of() {
            return spelled.get(spelled.size() - 1);
        }
    }

    /**
     * Two parts and what holding this one says of them.
     *
     * @param how what the connective composes, with the denial the tree was read under already
     *            applied: what is left holds no {@code not}, so a reader below asks this and never
     *            the operator the clause was written with
     */
    record Joined(List<Core> spelled, ConditionJoin how, ClauseExpr left, ClauseExpr right)
            implements ClauseExpr {

        public Joined {
            spelled = named(spelled);
        }
    }

    private static List<Core> named(List<Core> spelled) {
        if (spelled == null || spelled.isEmpty()) {
            throw new IllegalArgumentException("a shape is what some part of the tree was written as");
        }
        return Collections.unmodifiableList(new ArrayList<>(spelled));
    }

    /**
     * The shape of {@code clause}, stated where {@code positive} and denied where it is not.
     *
     * <p>The one mapping from a tree to a shape. A part this does not recognise as a connective is
     * a leaf, whatever it is — what a leaf means is the evaluator's, and which parts are
     * connectives is the language's.
     */
    static ClauseExpr of(Core clause, boolean positive) {
        return of(clause, positive, List.of());
    }

    private static ClauseExpr of(Core clause, boolean positive, List<Core> above) {
        List<Core> spelled = new ArrayList<>(above);
        spelled.add(clause);
        Conditions.Restated under = Conditions.restated(clause);
        if (under != null) {
            return of(under.condition(), under.denied() != positive, spelled);
        }
        if (clause instanceof Core.Binary bin) {
            // Stated, a conjunction gives both sides; denied, it gives the choice between their
            // denials. And the same the other way round, which is the whole of what a denial does
            // to a connective, and is why the denial is applied to what the connective composes.
            ConditionJoin joined = ConditionJoin.of(bin.op()).map(one -> one.under(positive))
                    .orElse(null);
            if (joined != null) {
                return new Joined(spelled, joined, of(bin.left(), positive, List.of()),
                        of(bin.right(), positive, List.of()));
            }
        }
        return new Leaf(spelled, positive);
    }
}
