package souther.compiler.check;

/**
 * How many times one reading has been copied by the case splits opened above it, and whether
 * another split may copy it again.
 *
 * <p>A reading is one evaluation against one context. Opening a split of {@code width} arms reads
 * what stands under it once per arm, under what choosing that arm settles, so the readings below it
 * are the readings above it copied {@code width} times. Nested splits multiply: widths
 * {@code w1, w2, ... wn} down one path make {@code w1 * w2 * ... * wn} copies of the innermost
 * reading. That product is what this bounds, and it is the one quantity every reader that opens a
 * split has in common.
 *
 * <p>Which is why it is not counted in what a reading costs. The walk over a region copies a
 * reading of the body ({@link InvariantChecker}); the reading of what a value is derived from
 * copies an evaluation of the recipes ({@link DerivedBounds}, once #973 connects it). Those are
 * different work and are not worth the same, and a number naming one of them would be naming a cost
 * the other does not have. What they share is the copying, so the copying is what is bounded and
 * each reader spends it in its own units.
 *
 * <p><b>A split one arm wide is free.</b> It copies a reading once, which is the reading itself, so
 * it multiplies nothing and is opened wherever it stands. An or-pattern arm covering every case of
 * a sum is such a split, and refusing one under a factor already past the limit would refuse
 * precision that costs nothing.
 *
 * <p><b>The first split that is not one arm wide is opened however wide it is.</b> Its width is
 * what it costs and nothing multiplies it. Refusing it would leave a {@code match} over a sum of
 * more cases than the limit read nowhere at all, which is the reading this is bounding rather than
 * something it is protecting against. So the limit is on the multiplying, and one path is copied at
 * most the widest split on it or the limit, whichever is the larger.
 *
 * <p><b>A split is opened for all its arms or for none.</b> Opening it for as many arms as the
 * remaining room allows would make what a reading finds depend on the order the arms were written
 * in. It is also what lets a reading be identified by the context it is against: a split that was
 * opened puts every arm in a context of its own, and one that was refused leaves every arm in the
 * context the split stood in, so nothing is half in one and half in the other.
 *
 * <p><b>Refusing a split gives up the refinement and not the reading.</b> The arms are still read —
 * under the context the split stands in, rather than under what choosing each of them settles. What
 * is lost is precision; what is read is the same.
 *
 * <p><b>Each reader starts at one and spends independently.</b> A reader does not inherit what
 * another has spent, since that would make what one reading finds depend on which reader ran first.
 * So the limit bounds the copying <em>within</em> one reader, and the copying across readers
 * multiplies: a region walk that reached a factor of sixteen, whose arms hold a reading that
 * reaches sixteen of its own, has copied the innermost reading two hundred and fifty-six times.
 * That is an example and not a maximum — the first split on a path is opened however wide it is, so
 * two readings whose first splits are a hundred arms wide compose to ten thousand, and neither has
 * compounded. What the limit states is that no <em>depth</em> of nesting buys a further factor, not
 * that the analysis produces at most so many contexts.
 */
record ContextMultiplicity(int factor, int compoundingLimit) {

    /**
     * How far the splits down one path may compound before the rest is left to the run-time check.
     *
     * <p>Sixteen, which is what a sum of eight cases costs with one conditional inside an arm.
     * Below that, opening a {@code match} spends enough that a conditional written in a value
     * position inside one of its arms is refused — and that conditional was opened before this
     * check read {@code match}es at all, by lifting it out of the arm. A limit that turns a
     * construction which discharged into one that is owed is the reading getting worse at a shape
     * it was not asked about. It also lets a fourth conditional be opened where three were opened
     * before, which is the same limit spent on the shape it was written for.
     */
    static final int CONTEXT_COMPOUNDING_LIMIT = 16;

    /**
     * A factor past the limit is a state this holds and not one it refuses. The first split that is
     * not one arm wide is opened however wide it is, so a sum of a hundred cases leaves a reading
     * copied a hundred times under a limit of sixteen, and the splits below it are refused because
     * of it. Requiring {@code factor <= compoundingLimit} here would refuse the reading the limit
     * exists to admit.
     */
    ContextMultiplicity {
        if (factor < 1) {
            throw new IllegalArgumentException("a reading is copied at least once and this one was"
                    + " copied " + factor + " times");
        }
        if (compoundingLimit < 1) {
            throw new IllegalArgumentException("splits compound to at least one reading and this"
                    + " limit is " + compoundingLimit);
        }
    }

    /** One reading, copied by nothing yet, under the limit the check holds itself to. Where every
     * reader begins, and the reason each begins here is that spending is not shared between
     * them. */
    static ContextMultiplicity ofOneReading() {
        return new ContextMultiplicity(1, CONTEXT_COMPOUNDING_LIMIT);
    }

    /**
     * What the readings under a split {@code width} arms wide are copied to, or null where opening
     * it would compound past the limit.
     *
     * <p>Asked before the arms are entered, and about what opening the split <em>would</em> come to:
     * a limit read after the fact bounds the path before the widest split on it and not the path.
     *
     * <p>The same answer for every arm of the split, since a split is opened for all of them or for
     * none. What it answers is a value and not a subtraction, so arms do not spend against one
     * another and the order they are read in decides nothing.
     */
    ContextMultiplicity opening(int width) {
        if (width < 1) {
            throw new IllegalArgumentException("a split answers one of several and this one was"
                    + " given " + width + " to answer one of");
        }
        if (width == 1) {
            return this;
        }
        if (factor != 1 && factor > compoundingLimit / width) {
            return null;
        }
        return new ContextMultiplicity(factor * width, compoundingLimit);
    }
}
