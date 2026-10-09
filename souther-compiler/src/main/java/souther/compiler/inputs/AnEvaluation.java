package souther.compiler.inputs;

import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.ValueName;

import java.util.Objects;

/**
 * One evaluation of a call to a dependency a row stands in: which dependency, and which call of it
 * the model writes.
 *
 * <p><b>The call and not what it was handed.</b> A dependency is the outside world — a clock, a
 * counter handing out the next number — and two calls of one with one argument are two answers
 * that need not agree. Keyed by the dependency and its arguments, {@code nextId() > 5} written twice
 * would be one question, and the way through the first denied and the second held would be read as
 * no way at all.
 *
 * <p><b>A name is the evaluation it was bound to, and nothing else is.</b> {@code let y = x} is the
 * value {@code x} names, and {@code x + 1} is arithmetic over it. That a name is the first and not
 * the second is settled where names are given a meaning ({@link InputReads#answerAt}), and that is
 * the only place one of these is made: what is not known to be a call, or a name for one, has no
 * evaluation to be.
 *
 * <p>Which call is the construct of the model it is ({@link ModelOccurrence}), which is what the
 * two readings of a body agree about. A call to a dependency stands in the behavior's own body,
 * where the dependency was handed, so no copy of a helper holds one; one inside a block an
 * operation runs once per element is an evaluation per application, which the reader asking about
 * the element is the one to decline.
 */
public final class AnEvaluation {

    private final ValueName.Behavior dependency;
    private final ModelOccurrence call;

    AnEvaluation(ValueName.Behavior dependency, ModelOccurrence call) {
        this.dependency = Objects.requireNonNull(dependency, "an evaluation is of some dependency");
        this.call = Objects.requireNonNull(call, "an evaluation is of some call the model writes");
    }

    /** Which behavior the row stands in for, named as the provisioning names it. */
    public ValueName.Behavior dependency() {
        return dependency;
    }

    /** Which call of it. */
    public ModelOccurrence call() {
        return call;
    }

    /** Which call this is among the constructs of its body, as an identity spells it — and in
     *  which copy, where it stands in one. */
    public String spelled() {
        return "#" + call.origin().ordinal()
                + (call.lineage() instanceof ExpansionLineage.Original ? "" : " in " + call.lineage());
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof AnEvaluation that && dependency.equals(that.dependency)
                && call.equals(that.call);
    }

    @Override
    public int hashCode() {
        return Objects.hash(dependency, call);
    }

    @Override
    public String toString() {
        return dependency + spelled();
    }
}
