package souther.compiler.inputs;

import java.util.List;

/**
 * One thing a rule placed, and what became of it at every place the name it was written at reaches.
 *
 * <p>A name written at a sum stands under each of its cases, so one rule placed once has an answer
 * per case, and the answers need not agree — one case takes it and another is a case no row can
 * write. What is asked of the pair is that every one of them ends somewhere said out loud.
 *
 * <p><b>Never empty.</b> A seed with no outcomes would be a rule that went nowhere without anybody
 * saying so, which is the thing this exists to make impossible: where a name reaches no position,
 * that is an outcome and is written down as one. So a reader counting what a build took in never has
 * to read an absence, and a reader reporting a cause never has to invent one.
 */
public final class PlacementFiling {

    private final PlacementSeed seed;
    private final List<PlacementOutcome> outcomes;

    /**
     * Package-private, so the resolution is the way one of these is made.
     *
     * <p>Being non-empty is not the whole of what has to hold. A list of outcomes anybody can write
     * lets a name that stands under three cases come back having answered for one of them, which is
     * the silence this exists to remove — said out loud for the case it reached, and said nothing
     * about for the two it did not. So the list is not an argument a caller assembles: it is what
     * following the name against what the walk observed came to, and following it is here.
     */
    PlacementFiling(PlacementSeed seed, List<PlacementOutcome> outcomes) {
        if (seed == null) {
            throw new IllegalArgumentException("something was placed");
        }
        this.seed = seed;
        this.outcomes = List.copyOf(outcomes);
        if (this.outcomes.isEmpty()) {
            throw new IllegalArgumentException(
                    "`" + seed.address() + "` was placed and came to nothing, which is an answer "
                            + "somebody has to have given rather than one nobody gave");
        }
    }

    /** What was placed. */
    public PlacementSeed seed() {
        return seed;
    }

    /** What became of it at every place the name it was written at reaches. */
    public List<PlacementOutcome> outcomes() {
        return outcomes;
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof PlacementFiling it
                && seed.equals(it.seed) && outcomes.equals(it.outcomes);
    }

    @Override
    public int hashCode() {
        return java.util.Objects.hash(seed, outcomes);
    }

    @Override
    public String toString() {
        return seed.address() + " -> " + outcomes;
    }

    /** Where this placement was filed, which is empty where none of its outcomes was a filing. */
    public List<PositionId> filedAt() {
        return outcomes.stream()
                .filter(each -> each instanceof PlacementOutcome.Filed)
                .map(each -> ((PlacementOutcome.Filed) each).at())
                .toList();
    }

    /** Whether anything about this placement is still waiting on this compiler. */
    public boolean anythingUnresolved() {
        return outcomes.stream().anyMatch(each -> each instanceof PlacementOutcome.Unresolved);
    }
}
