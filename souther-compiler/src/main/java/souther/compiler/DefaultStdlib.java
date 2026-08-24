package souther.compiler;

import souther.compiler.check.StdlibLoader;
import souther.compiler.stdlib.Stdlib;

/**
 * The standard library this compiler ships, read once for the process.
 *
 * <p>A lifecycle and nothing else. Reading the library means parsing and resolving twelve modules,
 * which is worth doing once; that it is done once is a decision about this process and not a
 * property of the library, so it is made here rather than by {@link StdlibLoader}, which builds a
 * whole library every time it is asked and hands it over finished.
 *
 * <p>What it publishes is a complete {@link Stdlib} or nothing at all. The class initializer of the
 * holder runs the load to completion before {@link #get} can return, so there is no state here that
 * a reader could catch half written — which is what the library's previous home had, and what made
 * the order its own parts were built in something the rest of the compiler could depend on by
 * accident.
 *
 * <h2>Who may read this</h2>
 *
 * <p>Two kinds of caller, and no others (held by
 * {@code OnlyABoundaryOrAProcessConstantReadsTheDefaultLibraryTest}):
 *
 * <ul>
 *   <li><b>A boundary that begins a piece of work.</b> {@code query.Compilation} reads it as it
 *       starts, beside the other settings a compilation is held to for its whole life;
 *       {@code doc.ApiCommand} reads it because a command that lists the library is not downstream
 *       of a compile. Everything they reach is handed the value.
 *   <li><b>A rule table derived from the shipped library and nothing else.</b> {@code Combinators}
 *       and the four beside it turn the library's signatures into rules this compiler checks with.
 *       The result is a constant of this compiler — the same for every compilation, and the same
 *       under any backend — so threading it from a construction site would put a value in a dozen
 *       signatures to say something none of them varies in.
 * </ul>
 *
 * <p>Anything that depends on which compilation is running takes a {@link Stdlib} as a value.
 */
public final class DefaultStdlib {

    private DefaultStdlib() {
    }

    /** Loaded when first asked for, not when this class is mentioned. A compiler doing work that
     *  never reads the library — formatting a source, printing a version — does not pay for it. */
    private static final class Holder {
        private static final Stdlib INSTANCE = StdlibLoader.load();
    }

    /** The library. */
    public static Stdlib get() {
        return Holder.INSTANCE;
    }
}
