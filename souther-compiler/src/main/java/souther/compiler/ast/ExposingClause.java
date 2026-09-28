package souther.compiler.ast;

import java.util.List;

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
 * {@link Ast.Module#published}: the module's own declarations that may be published, each asked
 * whether this clause {@link #admits} it. Asked one declaration at a time and never answered as a
 * set of names, so that nothing the clause writes can publish a name the module does not have to
 * publish — an entry naming an import, a value an attached file declares or a core module's
 * {@code private let} admits nothing, because nothing asks about it (spec
 * §only-a-modules-own-declarations-are-published).
 *
 * <p>The way is one direction only: nothing reads the clause back out of what is published. The two
 * differ where a rule turns on the author having named a declaration — a composition named by the
 * clause states its output there, and one published because no clause was written keeps its inferred
 * one.
 */
public sealed interface ExposingClause {

    /**
     * Whether this clause lets the module publish {@code declaration}, one of the module's own
     * declarations that may be published at all.
     *
     * <p>A clause names types at type granularity, so an entry written {@code Amount.decoder}
     * admits {@code Amount}.
     */
    boolean admits(String declaration);

    /** The module writes no {@code exposing} clause. */
    record Omitted() implements ExposingClause {

        /** The one of these there is: it holds nothing, so a second instance would be a second name
         *  for one answer. */
        public static final Omitted INSTANCE = new Omitted();

        @Override
        public boolean admits(String declaration) {
            return true;
        }
    }

    /** The module writes a clause, with these entries. Empty for {@code exposing ()}. */
    record Written(List<String> entries) implements ExposingClause {

        public Written {
            entries = List.copyOf(entries);
        }

        @Override
        public boolean admits(String declaration) {
            for (String entry : entries) {
                int dot = entry.indexOf('.');
                if ((dot < 0 ? entry : entry.substring(0, dot)).equals(declaration)) {
                    return true;
                }
            }
            return false;
        }
    }

    /**
     * The entries named by the clause, in the order they are written; none where no clause is
     * written.
     *
     * <p>What the author wrote and nothing more. Whether a name is published is
     * {@link Ast.Module#published}, and an empty answer here says nothing about it.
     */
    default List<String> named() {
        return this instanceof Written written ? written.entries() : List.of();
    }
}
