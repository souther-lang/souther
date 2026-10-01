package souther.compiler.ast;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;

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
 * {@link Ast.Module#published}: the module's own declarations that may be published, each put to
 * the question {@link #admitting} makes. Asked one declaration at a time and never answered as a
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
     * Whether this clause lets the module publish a declaration, asked of one of the module's own
     * declarations that may be published at all.
     *
     * <p>A clause names types at type granularity, so an entry written {@code Amount.decoder}
     * admits {@code Amount}.
     *
     * <p>A question to ask of each declaration rather than a single answer, because it is asked of
     * every one the module makes: what the entries name is read once, where the question is made,
     * and not again for each declaration.
     */
    Predicate<String> admitting();

    /** The module writes no {@code exposing} clause. */
    record Omitted() implements ExposingClause {

        /** The one of these there is: it holds nothing, so a second instance would be a second name
         *  for one answer. */
        public static final Omitted INSTANCE = new Omitted();

        @Override
        public Predicate<String> admitting() {
            return _ -> true;
        }
    }

    /** The module writes a clause, with these entries. Empty for {@code exposing ()}. */
    record Written(List<String> entries) implements ExposingClause {

        public Written {
            entries = List.copyOf(entries);
        }

        @Override
        public Predicate<String> admitting() {
            Set<String> named = new HashSet<>();
            for (String entry : entries) {
                int dot = entry.indexOf('.');
                named.add(dot < 0 ? entry : entry.substring(0, dot));
            }
            return named::contains;
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
