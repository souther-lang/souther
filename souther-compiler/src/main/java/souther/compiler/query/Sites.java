package souther.compiler.query;

import souther.compiler.ast.Hir;
import souther.compiler.sites.AuthoredSites;

/**
 * Where a module's source was written, occurrence by occurrence.
 *
 * <p>Asked of the resolved module and of nothing below it, which is what makes the answer about what
 * the author wrote rather than about what a pass made of it (ADR-0102).
 */
public final class Sites {

    private Sites() {}

    /**
     * Every expression occurrence {@code name}'s source was written with.
     *
     * <p>Absent where two of them could not be told apart. The reason is not carried into the graph
     * because there is no reader for it: an occurrence that cannot be named is a fact about this
     * compiler and not about the module, so what a consumer does is answer nothing — an editor that
     * asks what is at a position is told nothing is, and everything it can answer from the syntax
     * alone it still answers. {@link AuthoredSites#of} says which of the two refusals it was, for
     * whoever is looking into it.
     *
     * <p>Absent, too, where the module does not resolve. A source that will not resolve has no
     * settled reading of its names, and an occurrence found in one that has not is an occurrence
     * whose meaning is about to change.
     */
    public record Authored(String name) implements Key<AuthoredSites> {

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<AuthoredSites> compute(Db db) {
            Answer<Hir.Module> resolved = db.ask(new Names.Resolved(name));
            if (!resolved.present()) {
                return Answer.absent();
            }
            return AuthoredSites.of(resolved.value()) instanceof
                    AuthoredSites.Census.Identified(AuthoredSites sites)
                    ? Answer.of(sites) : Answer.absent();
        }
    }
}
