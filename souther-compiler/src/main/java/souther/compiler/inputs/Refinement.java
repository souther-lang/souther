package souther.compiler.inputs;

import souther.compiler.types.TypeSymbol;

/**
 * A narrowing of which values may stand at a position, which does not move to another position.
 *
 * <p>The distinction between this and a step of a path is the whole of what it is for. A field and
 * an element go somewhere: the value at the end of one is inside the value at the start of it. A
 * refinement goes nowhere — {@code d@Approved} is the same value {@code d} is, read as the case it
 * turned out to be — and what it buys is that the positions the case declares can be named at all.
 *
 * <p>Not one kind of narrowing. A sum states its cases and an optional states whether it holds
 * anything, and {@link Case} already reads both as distinctions of one kind; a refinement written
 * for cases alone would be a second reading of that, and the optional would arrive later as a
 * shape of its own with nothing to be an instance of.
 */
public sealed interface Refinement {

    /** How a path writes it, which is what a report names the position by. */
    String spelled();

    /**
     * The value turned out to be this case of the sum standing at the position.
     *
     * @param leaf the case, folded to a leaf as {@link Distinctions} folds the cases it reads
     */
    record SumCase(TypeSymbol leaf) implements Refinement {

        @Override
        public String spelled() {
            return leaf.name();
        }
    }

    /**
     * The optional standing at the position holds a value, or holds none.
     *
     * <p>{@code Some} refines the position to what the optional holds, and does not descend to it:
     * what an optional holds is at no name of its own, exactly as what a newtype wraps is
     * ({@link TermPath}). So the position under it is {@code x@Some} and never {@code x@Some.value}
     * — the second would be a location this compiler invented, spelled by nothing else that reads
     * the same value.
     */
    record Presence(boolean present) implements Refinement {

        @Override
        public String spelled() {
            return present ? "Some" : "None";
        }
    }
}
