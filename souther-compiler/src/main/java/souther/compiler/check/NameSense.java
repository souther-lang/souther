package souther.compiler.check;

import souther.compiler.types.TypeKey;

import java.util.Set;

/**
 * What a name written in a module means, and which identities anything declares.
 *
 * <p>The two questions a written type reference is read with, and the only ones that are the same on
 * both sides of {@code Resolve}: which declaration a spelling denotes is decided from the names in
 * sight, and whether something declares an identity is a fact about the compilation. Neither reads a
 * declaration, so neither has to know which representation the declarations are in.
 *
 * <p>Held apart from {@link Symbols} and {@link SyntaxSymbols} rather than duplicated in each, and
 * narrower than either: a reader given one of these cannot reach a declaration at all, which is what
 * keeps a question that needs one from being answered against the wrong representation.
 */
public interface NameSense {

    /** What a name written here means. */
    TypeScope scope();

    /** Whether anything declares {@code name} — this compilation or the language. */
    boolean declares(TypeKey address);

    /** The names one module declares. For a report offering what the author might have meant. */
    Set<String> declaredNamesIn(String module);
}
