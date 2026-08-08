package souther.compiler.check;

import souther.compiler.types.BoundaryInput;
import souther.compiler.types.BoundaryOutput;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * What a behavior takes and what it answers, as the shapes a decoder and an encoder are built for.
 *
 * <p>The witness is what a signature is, and the types are read off it. Holding both would make a
 * new thing to keep true — that they agree — and the crossing is one-way on purpose: a signature
 * always yields its types, and a type becomes a signature only by going through the walk that
 * admits it.
 *
 * <p>That is why this is not a record. A public canonical constructor would let anything below the
 * check assemble a signature out of shapes nothing admitted — a {@code Nominal} naming a type the
 * language declares of its own operations, say — and every reader below would take it for one the
 * compiler stands behind. The constructor is package-private, so {@link SignatureBoundary} and the
 * composition it is called from are the only places one is made, and the arrow from a type to a
 * signature runs through the walk rather than around it. The shapes themselves stay open: what
 * matters is what may be raised to a signature, not what may be described.
 */
public final class Sig {

    private final List<BoundaryInput> ins;
    private final BoundaryOutput out;

    Sig(List<BoundaryInput> ins, BoundaryOutput out) {
        this.ins = List.copyOf(ins);
        this.out = Objects.requireNonNull(out, "a signature answers something");
    }

    /**
     * What the parameters can arrive as, in order. The whole list: only the first stage of a
     * pipeline may have more than one, since {@code >->} hands a single value along and every stage
     * after the first takes one input (spec 14.1). {@link #in} is for those.
     */
    public List<BoundaryInput> ins() {
        return ins;
    }

    /** What the answer can leave as. */
    public BoundaryOutput out() {
        return out;
    }

    /** The types the parameters have, in order. */
    public List<Type> inputTypes() {
        List<Type> types = new ArrayList<>(ins.size());
        for (BoundaryInput in : ins) {
            types.add(in.type());
        }
        return types;
    }

    /** The type the answer has. */
    public Type outputType() {
        return out.type();
    }

    /** The sole input's type. Only call this for a stage after the first, which takes exactly one. */
    public Type in() {
        return ins.get(0).type();
    }

    /** Two signatures are the same when they carry the same shapes. The check's answers are compared
     *  to decide whether recomputing one changed anything, so this is what keeps a module that was
     *  reparsed into the same signatures from invalidating everything that read them. */
    @Override
    public boolean equals(Object other) {
        return other instanceof Sig sig && ins.equals(sig.ins) && out.equals(sig.out);
    }

    @Override
    public int hashCode() {
        return Objects.hash(ins, out);
    }

    @Override
    public String toString() {
        return "Sig[ins=" + ins + ", out=" + out + "]";
    }
}
