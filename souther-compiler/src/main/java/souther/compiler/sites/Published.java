package souther.compiler.sites;

/**
 * A name a module offers to whoever reaches it, and what kind of thing it names.
 *
 * <p>The kind is here because a reader shows one — an editor paints a type and a behavior with
 * different marks — and it is read off the declaration rather than guessed from the spelling. What a
 * module publishes says which names are offered and not which of these each is, so this is that
 * answered against what the module declares.
 */
public sealed interface Published {

    /** The name the offering module publishes it under. */
    String name();

    /** A data declaration. */
    record AType(String name) implements Published {}

    /** A behavior, written or composed. */
    record ABehavior(String name) implements Published {}

    /** A definition the module publishes for others to call. */
    record ADefinition(String name) implements Published {}
}
