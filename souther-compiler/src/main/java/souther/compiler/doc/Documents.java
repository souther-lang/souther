package souther.compiler.doc;

/**
 * The specification and the doc sets on the class path, as the one set of documents a reader asks.
 *
 * <p>A reader has one question and these have one answer between them: a listing gives the names
 * from both, a search ranks both and sorts once, and a name resolves against both. So the names are
 * one name space, and it is here that it is one — each document keeps its own names, and nothing
 * below this holds both to look at them together.
 *
 * <p>Which is why the uniqueness of a name is checked here. Each document refuses two of its own
 * names that come together under either fold, and neither can say anything about the other's. A
 * specification anchor {@code cli-commands} and a shipped topic {@code cli/commands} are two names
 * to read by and one name to resolve, and whichever the search asked for first would win, quietly,
 * by the order this code happens to ask in. That is not an order to settle it by, and there is no
 * order that would be: one of the two documents would be unreachable by the name it publishes.
 */
final class Documents {

    private final Caller caller;
    private final SpecDocument spec;
    private final LibraryDocs shipped;

    /**
     * The two of them, refusing a name they would both answer for.
     *
     * <p>The caller is held here rather than passed beside this. Both documents are spelled for a
     * caller when they are read, so a set is already one caller's, and a reader handed the set and
     * told a different caller would be offered what it cannot do.
     */
    Documents(Caller caller, SpecDocument spec, LibraryDocs shipped) {
        // One way round is every collision: a key both hold is a spec name, so asking the shipped
        // topics for each of the specification's names is asking about all of them.
        for (String name : spec.names()) {
            LibraryDocs.Topic topic = shipped.named(name);
            if (topic != null) {
                throw new IllegalStateException("a specification name and a shipped topic are the"
                        + " same words: `" + name + "` and `" + topic.name() + "`");
            }
        }
        this.caller = caller;
        this.spec = spec;
        this.shipped = shipped;
    }

    /**
     * The bundled specification and everything {@code loader} carries, answered as {@code caller}.
     *
     * <p>This reads the specification and every shipped doc set, which is what a set costs to make
     * and is why one is made for as long as it will be asked from rather than for each question.
     * Nothing it is built from moves while a process runs.
     */
    static Documents on(Caller caller, ClassLoader loader) {
        return new Documents(caller, SpecDocument.bundled(caller), LibraryDocs.on(loader, caller));
    }

    /** Who these were read for, and who is to be offered what they can do next. */
    Caller caller() {
        return caller;
    }

    SpecDocument spec() {
        return spec;
    }

    LibraryDocs shipped() {
        return shipped;
    }
}
