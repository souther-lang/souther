package souther.compiler.query;

import java.util.List;

/**
 * One question about one thing, and the code that answers it.
 *
 * <p>A key is a value: two keys that ask the same question are equal, which is what lets the engine
 * recognise the question it has already answered. Implementations are records, so that comes for
 * free — and a key holds only what identifies the question, never a compilation, a registry or a
 * position, because anything held here would be part of the question's identity.
 *
 * <p>The answer lives on the key rather than in a dispatch table somewhere, so one class is one
 * question: what it is, what it reads, and what it does when it cannot answer are in one place. A
 * key reaches everything else it needs by asking {@link Db}, which is what makes the read
 * observable — nothing else in the compiler can see what a pass depended on.
 */
public interface Key<T> {

    /**
     * Answers this question, asking {@code db} for whatever else it needs. Every read must go
     * through {@code db}: an answer computed from something reached another way is not recorded as
     * a dependency, so nothing would know to recompute it.
     */
    Answer<T> compute(Db db);

    /**
     * The module this question is about, or null when it is about the compilation as a whole.
     *
     * <p>This is how a report finds its file. A key answered while some other module was being
     * compiled still belongs to the module it names — an error in an imported module is that
     * module's, published on that module's document, not on its importer's. Nothing else in the
     * graph knows where an answer came from, so a key that is about one module says so.
     */
    default String module() {
        return null;
    }

    /**
     * The source this question is about, when it is about a source rather than a module — an
     * {@code examples for} file declares no module of its own, so a problem with it has no module
     * name to be found by. Null otherwise, and the module's own source is used instead.
     */
    default String sourceId() {
        return null;
    }

    /**
     * The answer when this question is reached while it is already being answered — the key depends,
     * through some chain, on itself.
     *
     * <p>{@code cycle} is every key being answered at that moment, outermost first. This key is in
     * it, once, at the point the chain came back round to it; it is not repeated at the end. The
     * keys before it are the ones that asked, which need not be part of the cycle at all.
     *
     * <p>An answer given here is handed to the caller that asked and nothing more. Every key that
     * took part in the cycle is left uncomputed, so this answer is not kept, and the reports it
     * carries are not there afterwards to be collected through {@link Db#allReports()}. A caller
     * reading reports off the answer it was handed sees them; one reading them back from the store
     * does not. This is not a way to turn a cycle into a diagnostic.
     *
     * <p>A key kind that can be part of a cycle must say what a cycle means for it: modules that
     * import each other, helpers that call each other. Left unimplemented it is a programming error,
     * because the alternative is answering with something arbitrary and letting a later pass make
     * sense of it.
     */
    default Answer<T> onCycle(List<Key<?>> cycle) {
        throw new IllegalStateException(describeCycle(cycle));
    }

    /**
     * What the default answer to a cycle says: the keys that only asked, then the cycle itself,
     * closing where it came back round.
     */
    private String describeCycle(List<Key<?>> cycle) {
        // Where this key first appears is where the chain closes, and there is only one place to
        // find: the ask that would put a key on the chain a second time is the ask that is answered
        // here instead, so no two keys in the chain are equal.
        int closes = cycle.indexOf(this);
        if (closes < 0) {
            // Not a shape of cycle: a chain that does not hold the key it closed on says nothing
            // about what depends on what, and whether this key depends on itself is not something
            // it can be read for.
            return "a query cycle was reported for " + this
                    + ", but its dependency chain does not contain it: " + cycle;
        }
        StringBuilder said = new StringBuilder("the query ").append(this)
                .append(" depends on itself and says nothing about what that means.");
        if (closes > 0) {
            said.append("\n  asked by:");
            for (Key<?> asker : cycle.subList(0, closes)) {
                said.append("\n    ").append(asker);
            }
        }
        said.append("\n  cycle:");
        for (Key<?> member : cycle.subList(closes, cycle.size())) {
            said.append("\n    ").append(member);
        }
        return said.append("\n    -> back to ").append(this).toString();
    }
}
