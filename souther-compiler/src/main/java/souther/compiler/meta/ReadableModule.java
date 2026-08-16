package souther.compiler.meta;

import souther.compiler.ast.Ast;
import souther.compiler.types.ValueName;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * A module this compiler restored from an artifact and then checked: everything an importer needs to
 * build against it, and nothing that was still being worked out.
 *
 * <p>Only reachable through {@link Readback.Ready}, which is what makes it mean anything. Holding
 * one is holding a module whose import lines have been read; there is no value for a module that was
 * decoded and not checked, so the reader that took the first and skipped the second cannot be
 * written.
 *
 * <p>The three are one fact and travel together. The module no longer says what its bare names mean
 * — the lines that said so are dropped once read — so {@code libraryNames} is the only thing that
 * does, and a reader holding the module without it resolves an invariant's bare names against
 * nothing. Which behaviors are injection targets is not written in any declaration and does not
 * survive as source, so it cannot be worked out again from the module either.
 *
 * <p>Told apart from {@link PublishedUniverse.Read}, which is a stage further on: that one holds a
 * module every name of which has been answered, against a universe of other modules. This is what
 * one artifact gives before any of that is asked.
 */
public record ReadableModule(Ast.Module module, Set<String> injectedBehaviors,
                             Map<String, ValueName.Stdlib> libraryNames) {

    /** Copied, because this is an answer a compilation remembers and an answer it remembers is a
     *  value. */
    public ReadableModule {
        injectedBehaviors = Collections.unmodifiableSet(new LinkedHashSet<>(injectedBehaviors));
        libraryNames = Collections.unmodifiableMap(new LinkedHashMap<>(libraryNames));
    }
}
