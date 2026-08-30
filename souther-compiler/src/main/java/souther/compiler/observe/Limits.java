package souther.compiler.observe;

import java.util.List;

/**
 * How much of a value an observation keeps.
 *
 * <p>Reading a decoded value into {@link ObservedValue} takes it out of the class loader that built it,
 * which is why the observation exists. It does not, on its own, bound how big the result is — a row may
 * hand a behavior a list of ten thousand lines, and a query answer holding that keeps it for as long as
 * the answer is memoised. So the walk stops at these limits and records what it dropped.
 *
 * <p>Nothing here changes what a value means. A walk directed by these produces the value it read
 * or says it stopped, and {@link #admits} answers whether a value already read whole is one these
 * numbers would have kept — so widening them lets more values be kept and makes no value mean
 * anything else.
 *
 * @param maxDepth    how deep the walk goes before a subtree becomes {@link ObservedValue.Truncated}
 * @param maxNodes    how many nodes the whole observation may hold
 * @param maxElements how many elements of one collection are kept
 * @param maxText     how many characters of one string are kept
 */
public record Limits(int maxDepth, int maxNodes, int maxElements, int maxText) {

    /** What an example row's inputs are observed under. Wide enough for a domain value written by hand,
     * narrow enough that a pathological fixture cannot sit in the query graph. */
    public static final Limits DEFAULT = new Limits(12, 2000, 64, 1024);

    /** No bound at all, so what these admit is a value that is there in full: no part of it was
     * stopped by a limit and no part of it could not be read. */
    public static final Limits UNBOUNDED = new Limits(Integer.MAX_VALUE, Integer.MAX_VALUE,
            Integer.MAX_VALUE, Integer.MAX_VALUE);

    public Limits {
        if (maxDepth < 1 || maxNodes < 1 || maxElements < 0 || maxText < 0) {
            throw new IllegalArgumentException("limits must be positive: " + maxDepth + ", " + maxNodes
                    + ", " + maxElements + ", " + maxText);
        }
    }

    /**
     * Whether a value stated by a source text is one these limits would keep whole.
     *
     * <p>Asked of a value that was read without limits, which is what a comparison is made against:
     * what a text stated is settled once, and how much of it may be kept somewhere is a second
     * question with no say in the first. A value this refuses is carried nowhere as a shortened
     * value — what is carried instead is that it was not kept.
     */
    public boolean admits(Asserted stated) {
        return stoppedBy(stated) == null;
    }

    /**
     * Why a stated value is not one these limits keep whole, or null where it is.
     *
     * <p>The same walk as {@link #admits(Asserted)}, answering what it met rather than that it met
     * something. A value larger than these numbers is one a walk under them would have stopped, and
     * says so; a value holding something that could not be read says that instead, whatever its
     * size — the two are what a reader has to tell apart, since one is about how much was written
     * and the other about what could be made of it.
     */
    public Incompleteness.Code stoppedBy(Asserted stated) {
        return new Room().holds(stated, 0);
    }

    /**
     * Whether an observed value is whole and within these limits.
     *
     * <p>The same question of the other half of the pair. A value a walk under these limits produced
     * carries {@link ObservedValue.Truncated} where it stopped and {@link ObservedValue.Unknown}
     * where it could not read, and neither is a value — so this is false for both, and true for a
     * value that is there in full.
     */
    public boolean admits(ObservedValue observed) {
        return stoppedBy(observed) == null;
    }

    /** Why an observed value is not one these limits keep whole, or null where it is. */
    public Incompleteness.Code stoppedBy(ObservedValue observed) {
        return new Room().holds(observed, 0);
    }

    /**
     * What is left of the node budget as one value is read.
     *
     * <p>One budget for the whole value and not one per subtree, which is what the walk that
     * produces an observation counts ({@code ObservedValues}). A node is charged where a value
     * stands: an {@link Asserted.Value} is the observed value it holds rather than a node of its
     * own, so a scalar costs one whichever of the two it is read as.
     */
    private final class Room {

        private int budget = maxNodes;

        /** {@link Incompleteness.Code#VALUE_TRUNCATED} where there is no room for a node here: a
         *  walk under these limits would have stopped at exactly this one. */
        private Incompleteness.Code room(int depth) {
            return budget-- > 0 && depth <= maxDepth ? null : Incompleteness.Code.VALUE_TRUNCATED;
        }

        Incompleteness.Code holds(Asserted stated, int depth) {
            return switch (stated) {
                case Asserted.Value(ObservedValue value) -> holds(value, depth);
                case Asserted.Built built -> {
                    Incompleteness.Code stopped = room(depth);
                    for (Asserted field : built.fields().values()) {
                        stopped = stopped != null ? stopped : holds(field, depth + 1);
                    }
                    yield stopped;
                }
                case Asserted.Elements elements -> {
                    Incompleteness.Code stopped = elements.elements().size() > maxElements
                            ? Incompleteness.Code.VALUE_TRUNCATED : room(depth);
                    for (Asserted element : elements.elements()) {
                        stopped = stopped != null ? stopped : holds(element, depth + 1);
                    }
                    yield stopped;
                }
                case Asserted.Entries entries -> {
                    Incompleteness.Code stopped = entries.entries().size() > maxElements
                            ? Incompleteness.Code.VALUE_TRUNCATED : room(depth);
                    for (Asserted.Entry entry : entries.entries()) {
                        stopped = stopped != null ? stopped : holds(entry.key(), depth + 1);
                        stopped = stopped != null ? stopped : holds(entry.value(), depth + 1);
                    }
                    yield stopped;
                }
            };
        }

        Incompleteness.Code holds(ObservedValue observed, int depth) {
            Incompleteness.Code stopped = room(depth);
            if (stopped != null) {
                return stopped;
            }
            // What a walk under these limits already met, said as it says it: a value it stopped and
            // a value it could not read are two things, and which one this is is not a second
            // reading — it is the one the value carries.
            if (observed.unread() != null) {
                return observed.unread();
            }
            return switch (observed) {
                case ObservedValue.Text(String text) ->
                        text.length() <= maxText ? null : Incompleteness.Code.VALUE_TRUNCATED;
                case ObservedValue.Sequence(List<ObservedValue> elements) -> {
                    Incompleteness.Code met = elements.size() > maxElements
                            ? Incompleteness.Code.VALUE_TRUNCATED : null;
                    for (ObservedValue element : elements) {
                        met = met != null ? met : holds(element, depth + 1);
                    }
                    yield met;
                }
                case ObservedValue.Mapping(List<ObservedValue.Entry> entries) -> {
                    Incompleteness.Code met = entries.size() > maxElements
                            ? Incompleteness.Code.VALUE_TRUNCATED : null;
                    for (ObservedValue.Entry entry : entries) {
                        met = met != null ? met : holds(entry.key(), depth + 1);
                        met = met != null ? met : holds(entry.value(), depth + 1);
                    }
                    yield met;
                }
                case ObservedValue.Constructed constructed -> {
                    Incompleteness.Code met = null;
                    for (ObservedValue field : constructed.fields().values()) {
                        met = met != null ? met : holds(field, depth + 1);
                    }
                    yield met;
                }
                // A value with no parts, which the room above already accounted for.
                case ObservedValue.Bool _, ObservedValue.Integer _, ObservedValue.Decimal _,
                     ObservedValue.Temporal _, ObservedValue.Unit _, ObservedValue.Absent _ -> null;
                // Neither is a value: `unread` above answers for both, and this arm is what says
                // that a case added beside them has to be considered here rather than admitted.
                case ObservedValue.Truncated _, ObservedValue.Unknown _ ->
                        Incompleteness.Code.VALUE_UNREADABLE;
            };
        }
    }
}
