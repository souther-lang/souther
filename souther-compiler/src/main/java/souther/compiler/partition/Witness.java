package souther.compiler.partition;

/**
 * A value of a quantity that this compiler could write down, from one run of its order.
 *
 * <p>Composing and never deciding. {@link Occupancy} says what the run holds; this says what came
 * back when something went looking, and the two are apart because they differ: a run of strings
 * above a bound holds every string with that one as a prefix and this names none of them, since
 * which one it would be is a choice, and a choice made here puts a character nobody wrote into a row
 * somebody has to read.
 *
 * <p>Which is why {@link NotConstructed} is not "there is nothing here". Read that way, a search
 * that gave up took a coverage item away — the mistake ADR-0091 is about, said one order down.
 */
public sealed interface Witness {

    /** A value of the run, which the run holds. */
    record Found(Level level) implements Witness {

        public Found {
            if (level == null) {
                throw new IllegalArgumentException("a witness is a value");
            }
        }
    }

    /** Nothing was composed, which says nothing about what the run holds. */
    record NotConstructed() implements Witness {}

    Witness NONE = new NotConstructed();

    /** The value, or null where none was composed. */
    default Level level() {
        return this instanceof Found found ? found.level() : null;
    }

    /** A witness where {@code level} is one, and none where it is null. */
    static Witness of(Level level) {
        return level == null ? NONE : new Found(level);
    }
}
