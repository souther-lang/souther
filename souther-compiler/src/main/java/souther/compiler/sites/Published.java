package souther.compiler.sites;

/**
 * A name a module offers to whoever reaches it, and what kind of thing it names.
 *
 * <p>The kind is here because a reader shows one — an editor paints a type and a behavior with
 * different marks — and it is read off the declaration rather than guessed from the spelling. A name
 * on an {@code exposing} line says which name is offered and not which of these it is, so this is
 * that line answered against what the module declares.
 */
public sealed interface Published {

    /** The name, as it is written on the offering module's {@code exposing} line. */
    String name();

    /** A data declaration. */
    record AType(String name) implements Published {}

    /** A behavior, written or composed. */
    record ABehavior(String name) implements Published {}

    /** A definition the module publishes for others to call. */
    record ADefinition(String name) implements Published {}
}
