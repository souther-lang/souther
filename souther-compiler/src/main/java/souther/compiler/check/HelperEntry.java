package souther.compiler.check;

import souther.compiler.ast.DefinitionName;
import souther.compiler.ast.Hir;
import souther.compiler.types.ReachName;

/**
 * One declaration a module can reach, with the two coordinates that answer for it.
 *
 * <p>{@code reachedAs} is what a call reaches it by and carries the declaration it names;
 * {@code address} is where the module holds it, which is what a body is asked for by and what a
 * method is emitted under. They come apart for anything the module did not declare —
 * {@code souther.list} declares {@code foldFrom}, a module reaches it as {@code List.foldFrom} and
 * holds it at {@code List.foldFrom} — and the alias in that reach is nowhere in the declaration, so
 * neither coordinate is recoverable from the other.
 *
 * <p>Which is why they are one value. A table that answered the two out of separate maps would have
 * two statements of one correspondence to keep true; here the pairing is made once, where the entry
 * is built from what the declaration and the reading module say, and every index is an index of
 * this.
 */
public record HelperEntry(DefinitionName address, ReachName reachedAs, Hir.FnDef definition) {

    public HelperEntry {
        if (address == null || reachedAs == null || definition == null) {
            throw new IllegalArgumentException(
                    "a reachable declaration is a definition, where it is reached from and where it"
                            + " is held: " + address + " / " + reachedAs + " / " + definition);
        }
    }

    /**
     * The entry for {@code definition}, reached by {@code reference}.
     *
     * <p>The address comes from the reference, which is the direction that holds: where a module
     * holds what it reaches follows from how it reaches it. The other way round is what this whole
     * type exists to stop.
     */
    public static HelperEntry reached(ReachName reference, Hir.FnDef definition) {
        return new HelperEntry(DefinitionName.of(reference), reference, definition);
    }

    /** The entry for a definition the module wrote itself, which it reaches bare and holds under
     *  the name it wrote. */
    public static HelperEntry own(ReachName reference, Hir.FnDef definition) {
        return new HelperEntry(definition.address(), reference, definition);
    }
}
