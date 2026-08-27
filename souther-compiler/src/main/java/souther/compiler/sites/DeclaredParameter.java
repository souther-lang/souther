package souther.compiler.sites;

import souther.compiler.diag.Region;

/**
 * A parameter an implementation names, and what the declaration above it says arrives there.
 *
 * <p>{@code writtenAt} is the name in the {@code let}, not the one in the signature — it is where a
 * reader is looking and where anything shown about it belongs.
 *
 * <p>{@code heldToARule} is whether the type has an invariant of its own. It travels with the type
 * rather than being asked for separately, because the two are one thing to a reader: what arrives
 * here is a {@code Draft}, and a {@code Draft} is not any record of those fields.
 */
public record DeclaredParameter(Region writtenAt, TypeFact type, boolean heldToARule) {
}
