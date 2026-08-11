package souther.compiler.partition;

import souther.compiler.check.Shape;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeView;
import souther.compiler.types.Type;

/**
 * A position the partition derivation may be asked about, and proof that it is one.
 *
 * <p>Holding one of these is the proof. The derivation asks whether a position divides, and answers
 * that it does not — {@code Absent} — only where it has looked everywhere there was to look. What
 * "everywhere" is depends on the position being one a value can stand at in the first place, and
 * that premise used to be nowhere: the walk took a {@link Type}, and a type it had no arm for fell
 * through the bottom of a chain of {@code if}s into the same answer as a position the model really
 * does not divide.
 *
 * <p>So the premise is the input's type rather than a check the walk repeats. A shape outside the
 * set cannot be carried here, so nothing downstream has to ask again, and {@code Absent} needs only
 * the evidence phases to have been exhausted.
 *
 * <p><b>The set is this package's, not the boundary's.</b> Which types reach a behavior's parameter
 * and which reach a data's field are two rules that disagree — an {@code Option} may be a field and
 * may not be a parameter — and neither of them is the question "what may a partition be derived
 * from". Deriving this set from either would make a change over there silently change what is
 * measured over here. Written out, a boundary that starts admitting a new shape stops this compiling
 * until the partition semantics of that shape have been decided.
 */
public record PartitionInput(TypeView view, Shape.PartitionInputShape shape) {

    /**
     * How {@code type} is read at a position the derivation is about.
     *
     * <p>Exhaustive over {@link Shape}, with no {@code default}: a sixteenth case stops this
     * compiling rather than arriving somewhere further down as a position nothing divides.
     */
    public static PartitionInput of(Type type, Symbols symbols) {
        TypeView view = TypeView.of(type, symbols);
        return new PartitionInput(view, admitted(view));
    }

    private static Shape.PartitionInputShape admitted(TypeView view) {
        return switch (view.shape()) {
            case Shape.PartitionInputShape admissible -> admissible;
            // Refused where a signature or a field is read, each by an exhaustive switch of its own
            // (SignatureBoundary, CodecShape), so a value of one reaching here is this compiler
            // disagreeing with itself about what a position can be — not a model to report on.
            case Shape.Cases _, Shape.Tuple _, Shape.Function _, Shape.Uninhabited _,
                 Shape.Bottom _, Shape.Erroneous _, Shape.Undecided _ ->
                    throw unreachableInput(view);
        };
    }

    /**
     * A shape that cannot stand at a position and did.
     *
     * <p>Not a refusal, not a derivation that stopped, and nothing a reader of a model can act on.
     * The boundary that admits what crosses and this one are separate exhaustive readings, and one
     * of them has let through what the other says cannot arrive.
     */
    private static IllegalStateException unreachableInput(TypeView view) {
        return new IllegalStateException(
                "`" + Type.show(view.declared()) + "` reads as " + view.shape()
                        + " at a position a partition is derived from; the boundary that admits a"
                        + " position and this disagree about what may stand at one");
    }
}
