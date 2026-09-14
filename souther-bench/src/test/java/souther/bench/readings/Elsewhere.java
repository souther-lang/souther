package souther.bench.readings;

/**
 * A place that answers, on a way to a reading that does not start at the stage.
 *
 * <p>Written and reached, so that a walk over the classes finds it and finds what it reads. What it
 * is not is anywhere the stage can arrive: nothing here is called from there, directly or through
 * anything else.
 *
 * <p>Here because a walk backwards from a reading meets whatever is on the way to that reading,
 * wherever the way begins. Recorded on being met, this would count as standing on a way from the
 * stage — and an entry naming it would look like a boundary doing its job while the stage went past
 * somewhere else entirely.
 */
public final class Elsewhere {

    private Elsewhere() {}

    /** Answers the same kind of question the model's own authority does, for a caller of its own. */
    public static String spelling(Written.Names names, String name) {
        return names.declaredNode(name) instanceof Written.Declared.Record record
                ? record.name() : name;
    }

    /** The caller, which is not the stage and is reached from nothing that is. */
    public static String asked(Written.Names names, String name) {
        return spelling(names, name);
    }
}
