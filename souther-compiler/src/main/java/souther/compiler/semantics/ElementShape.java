package souther.compiler.semantics;

import java.util.Collections;
import java.util.EnumSet;
import java.util.Set;

/**
 * What a construction of a container keeps of the elements of the container it was built from.
 *
 * <ul>
 * <li>{@code PERMUTES} — the same elements in another order. Everything survives.
 * <li>{@code SUBSET} — some of the same elements. Nothing new is there, so a property of every
 *     element survives.
 * <li>{@code MAPS} — one new element for each. Nothing is known of what they are.
 * <li>{@code COLLAPSES} — at most one new element for each. Neither the elements nor what a closure
 *     that answers about them said.
 * </ul>
 *
 * <p>Named for what it is the shape of. A word this broad is one the next thing with a shape
 * collides with, and this package will hold more propositions than it holds today.
 *
 * <p>How many there are is {@link SizeAgainstItsSource} and is stated beside this, not read off it. The two
 * agree for every construction the library has — the same elements in another order is as many,
 * some of them is no more — and that agreement is what made one enum look like enough. It ends at a
 * construction given two containers: {@code List.append(a, b)} holds neither {@code a}'s elements
 * alone nor {@code b}'s, and its size is still no less than either. A statement about the count that
 * has to be spelled as a statement about the elements cannot be made there.
 */
public enum ElementShape {
    PERMUTES, SUBSET, MAPS, COLLAPSES;

    /**
     * The shapes whose answer holds only elements it was given, so that what is true of every
     * element of the source is true of every element of the answer.
     *
     * <p>The one place this is said. A statement made of every element — an operation's guarantee,
     * a {@code List.all} a guard wrote — travels through these and no further, and a reader that
     * spelled the two shapes itself would be a second account of which constructions keep them.
     */
    public static final Set<ElementShape> THAT_KEEP_THE_ELEMENTS = Collections.unmodifiableSet(
            EnumSet.of(PERMUTES, SUBSET));
}
