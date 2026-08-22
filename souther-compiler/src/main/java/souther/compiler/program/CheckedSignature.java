package souther.compiler.program;

import souther.compiler.types.Type;

import java.util.List;

/**
 * What a behavior takes and what it answers, as the check settled them.
 *
 * <p>Written here rather than handing over the compiler's own {@code Sig}. That one carries how a
 * value crosses the boundary as well as its type — for a {@code Map} key, which reading admitted
 * it — and the witness it holds for that offers the vocabulary the name was admitted from, which is
 * the module as it was parsed. So a reader of a signature could reach the syntax tree, two hops
 * from a behavior's declared output. The types are what an output needs, and they name nothing
 * beyond themselves.
 */
public final class CheckedSignature {

    private final List<Type> takes;
    private final Type answers;

    CheckedSignature(List<Type> takes, Type answers) {
        this.takes = List.copyOf(takes);
        this.answers = answers;
    }

    /** Its inputs, in the order they were declared. */
    public List<Type> takes() {
        return takes;
    }

    /** What it answers with — for a behavior that can depart, the union of every case it may
     *  answer (spec §unmarked-sum). */
    public Type answers() {
        return answers;
    }

    @Override
    public String toString() {
        return takes + " -> " + answers;
    }
}
