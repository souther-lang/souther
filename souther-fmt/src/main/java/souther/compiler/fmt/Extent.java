package souther.compiler.fmt;

/**
 * Where something is in a laid-out canonical form: from {@code start} up to {@code end}, and the
 * two are equal where it is a position rather than a region.
 *
 * <p>Containment compares the ends. It is not the interval's characters as a set: a position is the
 * empty set of them, and every interval contains the empty set — a point past the end of the file
 * would be inside anything. What has to be checkable is that a position lies between the ends of
 * what holds it.
 */
record Extent(int start, int end) {

    Extent {
        if (start > end) {
            throw new IllegalArgumentException("an extent runs forwards: " + start + ".." + end);
        }
    }

    /** Whether {@code inner} lies within this one's ends. */
    boolean contains(Extent inner) {
        return start <= inner.start() && inner.end() <= end;
    }

    @Override
    public String toString() {
        return start + ".." + end;
    }
}
