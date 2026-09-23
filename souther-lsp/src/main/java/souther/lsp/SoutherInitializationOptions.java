package souther.lsp;

import souther.compiler.query.Adequacy;
import tools.jackson.databind.JsonNode;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.StringJoiner;

/**
 * What a client asked of this server in {@code initializationOptions.souther}, read against the
 * schema at {@code META-INF/souther/lsp/initialization-options-1.schema.json}.
 *
 * <p>Two ways of not being read, kept apart. A member the schema does not name is ignored and says
 * nothing: a client may send what a later server reads, and a server that complained about it would
 * be complaining about being older. A member the schema names, written with a value it does not
 * allow, is a setting its author believes took effect, so it is read as absent and the reason is
 * kept in {@link #unread} for the server to tell the client.
 *
 * <p>Told rather than refused. The handshake carries every feature of the session, and failing it
 * over one misspelt setting would take all of them away to report one of them.
 *
 * @param adequacy how much of what the rows cover to measure; {@link Adequacy.Level#OFF} unless a
 *                 level was named
 * @param unread   what was written in a member this server reads and could not be read, one
 *                 sentence each, in the order the members are read
 */
record SoutherInitializationOptions(Adequacy.Level adequacy, List<String> unread) {

    /** Nothing asked, and nothing to tell. */
    static final SoutherInitializationOptions NONE =
            new SoutherInitializationOptions(Adequacy.Level.OFF, List.of());

    SoutherInitializationOptions {
        unread = List.copyOf(unread);
    }

    /**
     * Reads {@code initializationOptions}, which may be absent or be something else entirely.
     *
     * <p>Absent is a member that is not there. A member written as JSON {@code null} is there, and
     * is a value like any other: the schema allows it nowhere, so it is read as unset and said to
     * be. What {@code initializationOptions} itself holds is the protocol's and other servers', so
     * only the {@code souther} member is held to the schema.
     *
     * <p>Every member this server advertises is read here, by a switch over {@link SoutherExtension}
     * with no default: a member added to that table is a member this method does not compile
     * without reading, so the handshake cannot announce an option nothing reads.
     */
    static SoutherInitializationOptions decode(JsonNode initializationOptions) {
        if (initializationOptions == null || !initializationOptions.isObject()) {
            return NONE;
        }
        JsonNode souther = initializationOptions.get("souther");
        if (souther == null) {
            return NONE;
        }
        if (!souther.isObject()) {
            return new SoutherInitializationOptions(Adequacy.Level.OFF, List.of(
                    "initializationOptions.souther is " + souther + ", which is not an object;"
                            + " none of it was read"));
        }
        List<String> unread = new ArrayList<>();
        Adequacy.Level adequacy = Adequacy.Level.OFF;
        for (SoutherExtension extension : SoutherExtension.values()) {
            JsonNode written = souther.get(extension.member());
            if (written == null) {
                continue;
            }
            Optional<String> allowed = switch (extension) {
                case ADEQUACY -> {
                    Optional<Adequacy.Level> named = written.isString()
                            ? Adequacy.Level.spelled(written.asString())
                            : Optional.empty();
                    if (named.isPresent()) {
                        adequacy = named.get();
                        yield Optional.empty();
                    }
                    yield Optional.of(levels());
                }
            };
            allowed.ifPresent(values -> unread.add("initializationOptions.souther."
                    + extension.member() + " is " + written + ", which is none of " + values
                    + "; it is read as unset"));
        }
        return new SoutherInitializationOptions(adequacy, unread);
    }

    private static String levels() {
        StringJoiner levels = new StringJoiner(", ");
        for (Adequacy.Level level : Adequacy.Level.values()) {
            levels.add(level.spelling());
        }
        return levels.toString();
    }
}
