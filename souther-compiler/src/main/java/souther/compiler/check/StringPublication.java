package souther.compiler.check;

/**
 * Whether a position's rules about the strings came out of the reading as sets.
 *
 * <p>A property of the position and of no rule of it. What the reading promises a reader is every
 * one of that position's string rules as the set it admits, and the promise is kept or it is not:
 * the sets are built out of one allowance ({@link souther.compiler.values.Allowance#realizeAll}), so
 * a rule affordable on its own goes unpublished beside one that was not. Answered per rule, which
 * of them a reader hears about would follow the order the building happened to take, and the
 * cheap one would be carrying a shortfall that is not about it.
 *
 * <p>So a position that is not complete publishes nothing about its strings anywhere: the parts
 * hold no entry for it ({@link ReadByClauses.OfAPart#aboutStrings}), and this is what says why. A
 * reader that finds nothing and asks nothing would be reading an absence as the model stating no
 * rule about the strings there, which is the opposite of what happened.
 */
sealed interface StringPublication {

    /** Every string rule of the position came out as the set it admits. */
    record Complete() implements StringPublication {}

    /**
     * They did not, so none of them is published.
     *
     * <p>Why the building stopped is not here. That is a fact about what the position was allowed
     * to build and is the allowance's to answer for; carried out with this, it would be a limit
     * reached on one rule standing for a group of them, and for a position given up on before this
     * asked anything it would be a limit nothing here ever reached.
     */
    record Incomplete() implements StringPublication {}
}
