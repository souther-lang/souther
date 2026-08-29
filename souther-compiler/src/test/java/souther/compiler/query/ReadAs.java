package souther.compiler.query;

import souther.compiler.check.ReadingPolicy;

/**
 * What these tests read a declaration under, which is what a compilation reads it under.
 *
 * <p>Nothing that reads a declaration makes a policy of its own — a policy made where it is needed
 * is one that can differ between two readings of the same declaration. A test is the caller here,
 * so it says which one, and unless it is about the fallback it says this.
 */
public final class ReadAs {

    /** The compilation's own, and not a copy of it: two numbers to keep equal is a thing to keep
     *  equal, and there is nothing here to go stale. */
    public static final ReadingPolicy THE_COMPILATION_DOES = Front.Reading.STANDARD;

    /**
     * A limit no choice fits under, so every one of them is merged into the product containing it.
     *
     * <p>What a reading of these was before it held its alternatives apart, and the only way that
     * reading is reached at all: nothing written in this repository expands far enough to fall back
     * to it at the limit a compilation sets, so a test that wants it says so.
     */
    public static final ReadingPolicy MERGING_WHAT_A_CHOICE_LEAVES = new ReadingPolicy(1, Front.Reading.STANDARD.scalePlacesLimit());

    private ReadAs() {
    }
}
