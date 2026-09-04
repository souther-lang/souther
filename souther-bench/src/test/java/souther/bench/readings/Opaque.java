package souther.bench.readings;

/**
 * An authority: it owns a question, reads whatever the answer needs, and hands back the answer.
 *
 * <p>Nothing of the caller's runs before it is finished and nothing raw comes back, so a walk that
 * arrives here has no reason to go on — which is the whole of what a boundary is.
 */
public final class Opaque {

    private Opaque() {}

    /** How a name is written where a reader meets one. */
    public static String spelling(Written.Names names, String name) {
        return names.declaredNode(name) instanceof Written.Declared.Record record
                ? record.name() : name;
    }
}
