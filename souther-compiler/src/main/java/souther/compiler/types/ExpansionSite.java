package souther.compiler.types;

/**
 * Which application an expansion is of, said in a way that does not depend on the walk that met it.
 *
 * <p>An expansion belongs to a call. Two calls of one helper write two sets of bindings and they are
 * two expansions; one call of it inside a helper that is itself expanded twice is two expansions as
 * well, and what tells those apart is the expansion around them rather than anything here.
 *
 * <p><b>Never the order the expansions were met in.</b> Which calls a pass expands is what the
 * policy it runs under decides: the tree a backend emits has the language's own operations expanded
 * into what they do, and the tree an analysis reads has them standing. So a counter over the
 * expansions of one body runs differently in the two, and a module helper expanded in both would be
 * one expansion in one tree and another in the other. Everything here comes from the source instead,
 * which is settled before either tree exists.
 */
public sealed interface ExpansionSite {

    /**
     * An application the source wrote.
     *
     * <p>The construct, which every application takes when it is read
     * ({@link CoverageOrigin}) and carries through every copy of it. A helper holding a call,
     * expanded at two of its own call sites, has that one call at both — and the two are told apart
     * by what they are inside.
     */
    record Written(CoverageOrigin call) implements ExpansionSite {

        public Written {
            if (call == null || !call.isWritten()) {
                throw new IllegalArgumentException(
                        "an application the source wrote is one this source counted: " + call);
            }
        }
    }

    /**
     * An application a name used as a value was expanded into.
     *
     * <p>No source wrote the application: the author wrote a name, and the block applying it is
     * what a body holds where a function value goes. So it is named by what made it necessary
     * ({@link EtaOrigin}) rather than by the application, there being none to name.
     */
    record Eta(EtaOrigin of) implements ExpansionSite {

        public Eta {
            if (of == null) {
                throw new IllegalArgumentException(
                        "a block a name was expanded into was expanded from some name");
            }
        }
    }
}
