package souther.compiler.partition;

import souther.compiler.types.TypeSymbol;

import java.util.List;

/**
 * Which declarations took in where a position stops, at each end.
 *
 * <p>What a run stopping at one of those ends is owed to, beside the line it lies against. The end
 * itself is what every rule about the position leaves together and is no one rule's
 * ({@link FarEnd.AtTheDomain}); who moved it is this, and it is carried from the reading that placed
 * the end rather than worked back out of the number afterwards.
 *
 * <p>Empty at an end nothing took in, which is where the position stops at its own type's rule or at
 * the order.
 *
 * @param below the declarations that took the low end in
 * @param above the same at the high end
 */
public record NarrowedEnds(List<TypeSymbol.AtModule> below, List<TypeSymbol.AtModule> above) {

    /** An end nothing took in, either way. */
    public static final NarrowedEnds NONE = new NarrowedEnds(List.of(), List.of());

    public NarrowedEnds {
        below = List.copyOf(below);
        above = List.copyOf(above);
    }

    /** The declarations that took one end in, told which end by which way the run lies from it. */
    public List<TypeSymbol.AtModule> at(souther.compiler.numeric.Towards inward) {
        return inward == souther.compiler.numeric.Towards.ABOVE ? below : above;
    }
}
