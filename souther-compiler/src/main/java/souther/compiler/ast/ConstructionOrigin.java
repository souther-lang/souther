package souther.compiler.ast;

/**
 * Where a construction standing in a body came from — what a permission check needs in order to tell
 * a construction the body makes from one that arrived in it already made.
 *
 * <p>Expansion is why the question has to be answered at all. A value is substituted at each
 * reference and a published body is spliced into its reader, so a construction written somewhere
 * else ends up as the same node one written here would be. Asking the node is the only way left.
 *
 * <p>The two ways in are held apart because they are not answered alike. A published body names the
 * module that published it, and that module hands over only what it declares: a construction of a
 * third module's type is nobody's to hand over, so the module is compared against the type's. A
 * value reference names no module — the construction belongs to the definition of the value, and the
 * behavior reading the name originates nothing whatever module declared the type.
 *
 * <p>Nothing is written here. What an origin is, is {@link Origins}' to say and this package's to
 * ask: the arms are declared there and so are the two questions a permission check has and the two
 * crossings that change an answer. A value of this type outside the package is a token — held by the
 * form that holds it, handed on by a rebuild, and asked about by asking the form
 * ({@link Hir.NewData#wasCarried}, {@link Hir.Apply#wasCarriedByValue}).
 *
 * <p>That is what makes the answer the node's rather than whoever has one in hand. A member here
 * would be a second place to ask and a second place to change: read through a pass's own reasoning
 * about a value it happens to hold, rather than through the form that knows what it is.
 */
public sealed interface ConstructionOrigin
        permits Origins.Own, Origins.Published, Origins.ByValue { }
