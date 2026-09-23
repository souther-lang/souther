package souther.lsp;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * The members of {@code initializationOptions.souther} this server reads, and so the ones it
 * advertises under {@code capabilities.experimental.souther}.
 *
 * <p>A client learns that a feature is here from its name being present, not from a version: a
 * member that is advertised is read, and one that is not is ignored. What values a member takes is
 * the initialization-options schema's to say, not this table's, so nothing here grows a version or
 * a list of values.
 *
 * <p>Advertised here and read in {@link SoutherInitializationOptions#decode}, which switches over
 * this table with no default, so a member added here does not compile until it is read.
 *
 * <p>The advertisement arrives in the answer to {@code initialize}, after the options were sent. It
 * tells a client what this server did with them, and what to send the next server it starts from the
 * same artifact; what a client may send before it has started one is in the schema the tooling
 * metadata names.
 */
enum SoutherExtension {

    /** How much of what the rows cover is measured and reported beside each behavior. */
    ADEQUACY("adequacy");

    private final String member;

    SoutherExtension(String member) {
        this.member = member;
    }

    /** The member's name, in {@code initializationOptions.souther} and in the advertisement. */
    String member() {
        return member;
    }

    /**
     * The value of {@code capabilities.experimental.souther}: every member, each with an empty
     * object. An object rather than {@code true}, so a member that comes to need something said
     * about it has somewhere to say it without its type changing under a client.
     */
    static Map<String, Object> advertised() {
        Map<String, Object> members = new LinkedHashMap<>();
        for (SoutherExtension extension : values()) {
            members.put(extension.member, Map.of());
        }
        return members;
    }
}
