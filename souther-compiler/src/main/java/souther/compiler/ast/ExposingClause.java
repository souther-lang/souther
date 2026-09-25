package souther.compiler.ast;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * What a module's header says about its {@code exposing} clause: that it writes none, or the entries
 * of the one it writes, in the order they are written.
 *
 * <p>Two states because the language gives them two meanings. A module that writes no clause
 * publishes every declaration it makes, and one that writes {@code exposing ()} publishes none
 * (spec §a-module-publishes-what-it-declares). Held as a list that is empty in both, the two are one
 * value, and every reader has to decide for itself which of them an empty list was.
 *
 * <p>This is what was written, and it is not what the module publishes. What it publishes is
 * {@link #publishedFrom}, worked out from this together with the declarations the module makes, and
 * the way is one direction only: nothing reads the clause back out of what is published. The two differ
 * where a rule turns on the author having named a declaration — a composition named by the clause
 * states its output there, and one published because no clause was written keeps its inferred one.
 */
public sealed interface ExposingClause {

    /**
     * The names this module publishes, out of {@code publishable}: every declaration of the module's
     * own that may be published at all.
     *
     * <p>A clause names types at type granularity, so an entry written {@code Amount.decoder} is
     * {@code Amount} here.
     */
    Set<String> publishedFrom(Set<String> publishable);

    /** The module writes no {@code exposing} clause. */
    record Omitted() implements ExposingClause {

        /** The one of these there is: it holds nothing, so a second instance would be a second name
         *  for one answer. */
        public static final Omitted INSTANCE = new Omitted();

        @Override
        public Set<String> publishedFrom(Set<String> publishable) {
            return Set.copyOf(publishable);
        }
    }

    /** The module writes a clause, with these entries. Empty for {@code exposing ()}. */
    record Written(List<String> entries) implements ExposingClause {

        public Written {
            entries = List.copyOf(entries);
        }

        @Override
        public Set<String> publishedFrom(Set<String> publishable) {
            Set<String> names = new LinkedHashSet<>();
            for (String entry : entries) {
                int dot = entry.indexOf('.');
                names.add(dot < 0 ? entry : entry.substring(0, dot));
            }
            return Set.copyOf(names);
        }
    }

    /**
     * The entries named by the clause, in the order they are written; none where no clause is
     * written.
     *
     * <p>What the author wrote and nothing more. Whether a name is published is
     * {@link #publishedFrom}, and an empty answer here says nothing about it.
     */
    default List<String> named() {
        return this instanceof Written written ? written.entries() : List.of();
    }
}
