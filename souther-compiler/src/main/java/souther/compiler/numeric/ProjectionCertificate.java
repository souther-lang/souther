package souther.compiler.numeric;

/**
 * Why the range handed over at a position is the whole of what the rules leave there.
 *
 * <p>A proof and not a reading of the world. Whether a range is the whole of what the rules leave is
 * settled by the rules, and holds or fails whatever anything here manages to show — so having none
 * of these says that nothing established it and says nothing at all about whether it holds. What
 * licenses an edge is having one; nothing licenses calling a range wider than the rules.
 *
 * <p>A sum with one member, because the theorem below is not the only one there is. A point checked
 * against every rule settles the value it stands at, which is a different proof about a smaller
 * thing; a range every rule follows from is the feasible set outright, which is this one's first
 * half doing the work on its own. Which proof was found is carried rather than reduced to a boolean,
 * so that a reader saying why an edge may be promised does not have to get it back from the fact
 * that it may be.
 */
public sealed interface ProjectionCertificate {

    /**
     * Every rule follows from the ranges together with the relations the closure holds between them,
     * and every position they name is spaced the same way.
     *
     * <p>Two things, and the second is what the first needs before it reaches a range. Rules that
     * follow from the ranges and the relations are rules those two together are the feasible set of:
     * nothing they admit is refused by any rule, and nothing the rules admit was dropped on the way.
     * But what is handed over is one range at a time and not the relations beside them, so being the
     * feasible set has to come back to a range — and that is the closure theorem. A difference-bound
     * system closed on itself has every end of every position reached by some point of it, so
     * intersecting the ranges with the relations projects back onto exactly the ranges.
     *
     * <p>The theorem is about a system whose positions are all of one kind. Where they all step, the
     * closed edges are whole numbers and the corner an end is read at is a point; where they all
     * fill, there is nothing an end has to be rounded onto. Mixed, a difference may be held at a half
     * while one of its ends can only be whole, and then the corner is not a point — which is why the
     * hypothesis is asked rather than assumed.
     *
     * <p>What the theorem also needs is that no relation can still carry one range onto another, and
     * that is not asked here: it is a property of every box a {@link ClosedState} hands back, held
     * whether or not its rounds settled, and asserted where the box is made.
     */
    record ByBoxAndClosedDifferences() implements ProjectionCertificate {}
}
