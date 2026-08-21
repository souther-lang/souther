package souther.compiler.numeric;

/**
 * Why the box this derives holds, at each position, exactly what the rules leave there.
 *
 * <p>About the box and not about the number a caller is handed at an end of it. The arithmetic here
 * is exact, and a bound at a value no decimal writes is rounded outward on the way out — so whether
 * the end handed over is the end the rules drew is a question about the writing, asked by whoever
 * does the writing. Certifying the box is one of the things an edge stands on and not the whole of
 * them.
 *
 * <p>A proof and not a reading of the world. Whether the box holds what the rules leave is settled by
 * the rules, and holds or fails whatever anything here manages to show — so having none of these says
 * that nothing established it and says nothing at all about whether it holds. What licenses an edge
 * is having one; nothing licenses calling the box wider than the rules.
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
     * Every rule follows from the box together with the relations the closure holds between its
     * positions, and every position they name is spaced the same way.
     *
     * <p>Two things, and the second is what the first needs before it reaches a range. Rules that
     * follow from the box and the relations are rules those two together are the feasible set of:
     * nothing they admit is refused by any rule, and nothing the rules admit was dropped on the way.
     * But a reader takes one position's bounds at a time and not the relations beside them, so being
     * the feasible set has to come back to a position — and that is the closure theorem: a
     * difference-bound system closed on itself projects onto exactly the interval each position's
     * own bounds describe, so intersecting the box with the relations gives the box back.
     *
     * <p>Which is the bounds being tight and not every one of them standing on a point. An end the
     * rules put a value at is one some point of the system carries; an end they hold a position away
     * from is where the position stops without arriving, and over values that fill there is no
     * greatest one below it to arrive at. {@code x < 1} leaves exactly the values under one and no
     * point of it has {@code x} at one, and the bound is the whole of what the rules leave all the
     * same. Reading tightness as attainment is how an edge nobody can stand on gets promised.
     *
     * <p>The theorem is about a system whose positions are all of one kind. Where they all step, the
     * closed edges are whole numbers and the corner an end is read at is a point; where they all
     * fill, there is nothing an end has to be rounded onto. Mixed, a difference may be held at a half
     * while one of its ends can only be whole, and then the corner is not a point — which is why the
     * hypothesis is asked rather than assumed.
     *
     * <p>What the theorem also needs is that no relation can still carry one position's bounds onto
     * another's, and
     * that is not asked here: it is a property of every box a {@link ClosedState} hands back, held
     * whether or not its rounds settled, and asserted where the box is made.
     */
    record ByBoxAndClosedDifferences() implements ProjectionCertificate {}
}
