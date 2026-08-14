package souther.compiler.observe;

/**
 * What an {@code example} row names itself.
 *
 * <p>A row used to carry its written description as a string that was allowed to be null, documented
 * as "the row's business-case name, or null". That is enough for a hint on a diagnostic already
 * anchored at the row, and not enough for anything that has to say <em>which</em> row it means from
 * outside the file the row is written in — a test that prepares an environment for one row, a
 * generated test named after one, a report line two runs are compared on. Those need a name, and a
 * name that is allowed to be absent is one a reader keys on and silently finds nothing under.
 *
 * <p>So the two are separated here rather than left to each reader. A {@link Named} row was written
 * with a name, and the compiler holds that name to being the only one of its behavior's rows carrying
 * it — so a reader that resolves a name against a behavior's rows finds one row or none, never two.
 * An {@link Unnamed} row was written without one: it can be shown, and it cannot be addressed from
 * outside. Nothing here can be built for a name that is written but says nothing; that is refused
 * where the row is written.
 *
 * <p>This is what a row names itself and not where it sits in a namespace. Which behavior's row it is
 * belongs to whatever holds the row — {@link RowOutcome#target()} is the one the compiler keeps — so
 * that a row and its behavior cannot be recorded as disagreeing about each other.
 */
public sealed interface RowIdentity {

    /** What a report writes to say which row this is. Not a key: see {@link Unnamed}. */
    String shown();

    /**
     * A row written with a name.
     *
     * <p>The name is the row's, and editing it is a rename of the row rather than a rewording of a
     * label: what a name is for is being said somewhere else, and the row that answers to a name is
     * the one carrying it now.
     */
    record Named(String name) implements RowIdentity {

        public Named {
            if (name == null || name.isBlank()) {
                throw new IllegalArgumentException("a row's name is text that names something");
            }
        }

        @Override
        public String shown() {
            return name;
        }
    }

    /**
     * A row written without a name, and which of its behavior's rows in one source it is.
     *
     * <p>The ordinal is for showing, and nothing outside the compiler can address a row by it. It
     * counts within one source, so a behavior exampled in a module and in an attached file has a
     * first row in each: what tells those apart is the source, which every report carries anyway. It
     * moves when a row of the same behavior is written above it, which is what a name would not do
     * and is the reason an unnamed row is not addressable rather than addressable by number.
     */
    record Unnamed(int ordinal) implements RowIdentity {

        public Unnamed {
            if (ordinal < 1) {
                throw new IllegalArgumentException("a row is the first of its behavior's or a later one");
            }
        }

        @Override
        public String shown() {
            return "#" + ordinal;
        }
    }

    /**
     * The identity of a row written with {@code written} as its name, or without one.
     *
     * <p>Writing no name and writing one that names nothing are two things, and only the first is a
     * row without a name. The second is refused where it is written, so nothing reaches here with
     * one; reading it as no name would turn a refused row into an unnamed one and hide the refusal
     * from whatever came next. It arrives here as what it is — a name that {@link Named} will not
     * hold — which is a defect in the compiler rather than a state of the source.
     *
     * @param written the name as the row wrote it, or null where the row wrote none
     * @param ordinal which of its behavior's rows in this source this is, counted from one
     */
    static RowIdentity of(String written, int ordinal) {
        return written == null ? new Unnamed(ordinal) : new Named(written);
    }
}
