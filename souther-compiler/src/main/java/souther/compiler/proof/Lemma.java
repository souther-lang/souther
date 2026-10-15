package souther.compiler.proof;

import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.OperationLaw;

import java.util.List;
import java.util.Objects;

/**
 * A statement about an operation the library writes in the language, to be proved against its
 * body, with what is to be proved of a walk the body makes on the way.
 *
 * <p>Stated and never taken: a lemma is an obligation, and only a proof of it makes it a law. What
 * a walk carries is stated as statements that hold at every step of it ({@link #carries}), over the
 * operation's arguments, the parts of what the walk carries and the part of its list it has walked
 * ({@link Slot}) — so a statement that what is carried holds something exactly where some walked
 * element meets the closure says it of every step, and of the whole list where the walk ends. A
 * statement naming {@link Slot.Every} holds of every value.
 *
 * @param states  what the operation's answer comes to, over its arguments by place
 * @param carries what holds of what a walk in the body carries at every step; empty where the
 *                body walks nothing
 */
public record Lemma(OperationLaw<Integer> states, List<LawProposition<Slot>> carries) {

    public Lemma {
        Objects.requireNonNull(states, "a lemma states something");
        carries = List.copyOf(carries);
    }
}
