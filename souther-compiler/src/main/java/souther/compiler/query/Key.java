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
     * through some chain, on itself. {@code cycle} is that chain, outermost first, ending at this
     * key's other occurrence.
     *
     * <p>A key kind that can be part of a cycle must say what a cycle means for it: modules that
     * import each other, helpers that call each other. Left unimplemented it is a programming error,
     * because the alternative is answering with something arbitrary and letting a later pass make
     * sense of it.
     */
    default Answer<T> onCycle(List<Key<?>> cycle) {
        throw new IllegalStateException(
                "the query " + this + " depends on itself and says nothing about what that means: "
                        + cycle);
    }
}
