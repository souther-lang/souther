package souther.compiler.ast;

/**
 * What a definition of a module is filed under here: the address its body is asked for by, and the
 * name a method is emitted under.
 *
 * <p>Not what the definition is. Which declaration it is a copy of is
 * {@link DefinitionRole.TakenOn#reachedAs}, and which module wrote it is
 * {@link Hir.FnDef#declaredIn}; this says where it sits among the definitions this module holds, and
 * nothing more. The two coincide for a module's own {@code let} and come apart for one it took on:
 * {@code souther.list} declares {@code foldFrom} and a module holds it at {@code List.foldFrom}.
 *
 * <p>Its own type because a bare string cannot say which of those it is. A spelling an author wrote,
 * a reference rendered, a declaration's name and an address among a module's definitions all render
 * as text, and a table keyed by text takes any of them — which is how a reference came to be joined
 * to a body by being spelled out.
 *
 * <p>So there is one way to get one: off the definition it addresses. A reference rendered cannot
 * become one, which is the direction this exists to close — a caller holding a
 * {@link souther.compiler.types.ReachName} reaches the definition through whatever answers
 * references, and takes the address off what it found.
 */
public record DefinitionName(String text) {

    public DefinitionName {
        if (text == null || text.isEmpty()) {
            throw new IllegalArgumentException("a definition is held under a name");
        }
    }

    /**
     * The address {@code definition} is held under.
     *
     * <p>The only way one is made. A factory over a string would be the same as the string, and the
     * point of this type is that the caller has to have the definition.
     */
    public static DefinitionName of(Hir.FnDef definition) {
        return new DefinitionName(definition.written().canonical());
    }

    /**
     * The same, for a definition read as a {@link Ast.FnDef} — before the front end has answered
     * anything about it.
     *
     * <p>What a module holds its definitions under is settled by the source, so it is the same
     * address at both representations and is read off either.
     */
    public static DefinitionName of(Ast.FnDef definition) {
        return new DefinitionName(definition.written().canonical());
    }

    /**
     * Where a module holds what it reaches by {@code reference}.
     *
     * <p>The one direction between the two that holds. How a module reaches a declaration decides
     * where it puts the method it emits for it, so an address follows from a reference; a reference
     * does not follow from an address, because the alias a library publishes an operation under is
     * part of the reach and is nowhere in the declaration. A reader holding an address and wanting
     * the reference asks whatever built the pair.
     */
    public static DefinitionName of(souther.compiler.types.ReachName reference) {
        return new DefinitionName(reference.rendered());
    }

    @Override
    public String toString() {
        return text;
    }
}
