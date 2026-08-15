package souther.compiler.diag;

import java.util.Objects;

/**
 * Where code this compile has no file for came from, and the name a reader here reaches it by.
 *
 * <p>Two facts about one body of code that are not the same fact, and neither is read off the other.
 * {@link #reachedBy()} is what a report writes — {@code Int.abs}, {@code lib.text}, {@code
 * lib.text.atLeast} — and is enough to look the code up by. Which arm it is says what kind of thing
 * this compile is without: a module somebody published, or the library the compiler ships. Nothing
 * reads the arm yet. It is here because the two have different futures — a published module may one
 * day carry where its source is and be linked to, and the library never will — and a single string
 * would have to be taken apart by spelling to tell them apart on the day one of them gains that.
 *
 * <p>What this does <em>not</em> say is which source a line and a column are read in. That is a
 * separate question with a separate answer ({@link SourcePos#sourceId()}), and reading one off the
 * other is what this exists to stop: a body copied from out of sight is read against the caller's
 * file, so it is out of sight and in a source of this compile at once.
 */
public sealed interface SourceProvenance {

    /** The name a reader here reaches the code by. Where what is out of sight is a whole module
     *  rather than something in one, the module's name is how it is reached, and the two coincide. */
    String reachedBy();

    /** Code in a module somebody else built and published, read back off the module path. */
    record APublishedModule(String reachedBy) implements SourceProvenance {

        public APublishedModule {
            Objects.requireNonNull(reachedBy, "code out of sight is reached by a name");
        }
    }

    /** Code in the standard library, which ships with the compiler and is in no source of any
     *  compile that calls it. */
    record TheStandardLibrary(String reachedBy) implements SourceProvenance {

        public TheStandardLibrary {
            Objects.requireNonNull(reachedBy, "code out of sight is reached by a name");
        }
    }

    /** The same provenance, reached by {@code name} instead — what a splice writes when it learns
     *  the name the call reaches, the parse having known only the module. The arm is kept: what
     *  kind of thing this compile is without does not change with how a caller spells its way in. */
    default SourceProvenance reachedBy(String name) {
        return switch (this) {
            case APublishedModule _ -> new APublishedModule(name);
            case TheStandardLibrary _ -> new TheStandardLibrary(name);
        };
    }
}
