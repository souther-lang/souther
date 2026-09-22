package souther.compiler.program;

import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;

/**
 * What a behavior takes and what it answers, as the check settled them.
 *
 * <p>Written here rather than handing over the compiler's own {@code Sig}. That one carries how a
 * value crosses the boundary as well as its type — for a {@code Map} key, which reading admitted
 * it — and the witness it holds for that offers the vocabulary the name was admitted from, which is
 * the module as it was parsed. So a reader of a signature could reach the syntax tree, two hops
 * from a behavior's declared output.
 *
 * <p>What an output needs is not only the type. Representation is a function of a value and the
 * position it stands at — an {@code Option} at a parameter and one nested in a list cross
 * differently, and a sum's alternatives travel as a bare tag or a discriminated object depending
 * on what they carry — so a reader asking how a value crosses reads {@link #inputs()} and
 * {@link #output()}, which are the checked boundary shape and carry that decision rather than
 * leaving it to be read off {@link Type} again. {@link #takes()} and {@link #answers()} stay for a
 * reader that only ever wanted the type.
 */
public final class CheckedSignature {

    private final List<CheckedBoundaryInput> inputs;
    private final CheckedBoundaryOutput output;

    CheckedSignature(List<CheckedBoundaryInput> inputs, CheckedBoundaryOutput output) {
        this.inputs = List.copyOf(inputs);
        this.output = output;
    }

    /** What each parameter can arrive as, in the order they were declared. */
    public List<CheckedBoundaryInput> inputs() {
        return inputs;
    }

    /** What the answer can leave as — for a behavior that can depart, the cases of the union it
     *  may answer (spec §unmarked-sum). */
    public CheckedBoundaryOutput output() {
        return output;
    }

    /** Its inputs' types, in the order they were declared. */
    public List<Type> takes() {
        List<Type> types = new ArrayList<>(inputs.size());
        for (CheckedBoundaryInput input : inputs) {
            types.add(input.type());
        }
        return types;
    }

    /** What it answers with — for a behavior that can depart, the union of every case it may
     *  answer (spec §unmarked-sum). */
    public Type answers() {
        return output.type();
    }

    @Override
    public String toString() {
        return takes() + " -> " + answers();
    }
}
