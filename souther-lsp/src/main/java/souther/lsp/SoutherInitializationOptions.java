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

    /** Reads {@code initializationOptions}, which may be absent or be something else entirely. */
    static SoutherInitializationOptions decode(JsonNode initializationOptions) {
        if (initializationOptions == null || !initializationOptions.isObject()) {
            return NONE;
        }
        JsonNode souther = initializationOptions.get("souther");
        if (souther == null || souther.isNull()) {
            return NONE;
        }
        if (!souther.isObject()) {
            return new SoutherInitializationOptions(Adequacy.Level.OFF, List.of(
                    "initializationOptions.souther is " + souther + ", which is not an object;"
                            + " none of it was read"));
        }
        List<String> unread = new ArrayList<>();
        Adequacy.Level adequacy = adequacy(souther.get(SoutherExtension.ADEQUACY.member()), unread);
        return new SoutherInitializationOptions(adequacy, unread);
    }

    private static Adequacy.Level adequacy(JsonNode written, List<String> unread) {
        if (written == null || written.isNull()) {
            return Adequacy.Level.OFF;
        }
        Optional<Adequacy.Level> named = written.isString()
                ? Adequacy.Level.spelled(written.asString())
                : Optional.empty();
        if (named.isPresent()) {
            return named.get();
        }
        StringJoiner levels = new StringJoiner(", ");
        for (Adequacy.Level level : Adequacy.Level.values()) {
            levels.add(level.spelling());
        }
        unread.add("initializationOptions.souther." + SoutherExtension.ADEQUACY.member() + " is "
                + written + ", which is none of " + levels + "; nothing is measured");
        return Adequacy.Level.OFF;
    }
}
