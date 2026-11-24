package souther.compiler.inputs;

/**
 * What a reading asked of the values an application handed to the names on the way to it: the
 * names, and the application it began on, which has the value each was handed or nothing where it
 * was handed none.
 *
 * <p>A reading that asked these and nothing else of what was handed comes to the same on any
 * reading whose answers they are, whatever else it was handed ({@link InputReads#handsAsAsked}).
 */
public final class HandedAnswers {

    /** What a reading that is not to be told from another by what it asked asked: it compared
     *  whole environments, or was run inside another watch. Holds of no reading. */
    public static final HandedAnswers UNTOLD = new HandedAnswers(null, AskedNames.NONE, false);

    /** What the application the reading began on handed, which is what each name asked was
     *  answered: a name is asked only where it was not handed again since. */
    private final BindingEnvironment.Handed began;
    private final AskedNames names;
    private final boolean toldApart;

    HandedAnswers(BindingEnvironment.Handed began, AskedNames names) {
        this(began, names, true);
    }

    private HandedAnswers(BindingEnvironment.Handed began, AskedNames names, boolean toldApart) {
        this.began = began;
        this.names = names;
        this.toldApart = toldApart;
    }

    /** The names asked. */
    AskedNames names() {
        return names;
    }

    /** Whether a reading that asked these is told from another by them. */
    public boolean toldApart() {
        return toldApart;
    }

    boolean holdsOf(BindingEnvironment other) {
        return toldApart && other.handedAgrees(began, names);
    }
}
