package souther.lsp;

import java.util.List;

/**
 * What tells a client that a {@link LspMethod} can be called.
 *
 * <p>Not every method is announced the same way, and some are announced by nothing at all, so this
 * is a set of alternatives rather than a capability name. A method whose absence from the handshake
 * is deliberate carries {@link None} with the reason it is absent, which is what separates a
 * decision from an omission — the two look identical in a hand-written capability map.
 *
 * <p>One advertisement may be shared by several methods: full document sync is one capability that
 * three notifications rely on, and no method holds it alone.
 */
public sealed interface Advertisement {

    /**
     * A field of the {@code capabilities} object the initialize result answers with.
     *
     * <p>Named by its path from the top of that object, because the protocol nests some of them:
     * {@code workspace.workspaceFolders} is a field of {@code workspace}, which other capabilities
     * share. The value is the field's whole value, not a flag: some capabilities are a boolean and
     * others an options object, and which one a capability takes is part of the capability rather
     * than something a caller decides.
     */
    record StaticCapability(List<String> path, Object value) implements Advertisement {

        public StaticCapability {
            path = List.copyOf(path);
            if (path.isEmpty()) {
                throw new IllegalArgumentException("a capability is a field, and a field has a name");
            }
        }

        /** A field at the top of the capabilities object. */
        public StaticCapability(String key, Object value) {
            this(List.of(key), value);
        }
    }

    /**
     * Announced after the handshake by {@code client/registerCapability} rather than by a field of
     * the capabilities object.
     *
     * <p>The method being registered is the one holding this, so it is not written here.
     */
    record DynamicRegistration(String id, Object registerOptions) implements Advertisement {
    }

    /** Nothing in the handshake tells a client about this method. */
    record None(Reason reason) implements Advertisement {
    }

    /** Why a method is answered without being announced. */
    enum Reason {

        /**
         * The handshake and its teardown. These are answered before any capability has been agreed,
         * and a server that could not answer them would never be asked anything else.
         */
        LIFECYCLE,

        /**
         * Defined by the protocol for every server, with no field in the capabilities object to
         * carry it. A client sends these knowing they may be ignored.
         */
        UNADVERTISED_PROTOCOL_METHOD,

        /**
         * Announced by a flag inside another method's capability rather than by one of its own. A
         * client learns that this is answered from the method it completes, so a field here would be
         * the same fact said twice and free to disagree with itself.
         */
        UNDER_ANOTHER_METHODS_CAPABILITY
    }
}
