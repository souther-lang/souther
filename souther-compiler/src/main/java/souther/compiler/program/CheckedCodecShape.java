package souther.compiler.program;

import souther.compiler.types.LeafScalar;
import souther.compiler.types.MapKeyRepresentation;
import souther.compiler.types.TypeSymbol;

/**
 * What a field carries across the boundary — projected from
 * {@link souther.compiler.derive.CodecShape}, which is where a field's codec is derived from its
 * declared type and position. A reader here does not ask again whether an optional here omits its
 * key or writes {@code null}: that is decided by which case holds it, {@link OptionOf} for the
 * field a {@code ?} stands on and {@link ListOf}/{@link SetOf}/{@link MapOf} for the element or
 * value an optional stands under, and neither arm leaves it for the reader to tell apart by looking
 * at {@link souther.compiler.types.Type} alone.
 */
public sealed interface CheckedCodecShape {

    /** A shape that is not an optional. Everything but an optional is one. */
    sealed interface Bare extends CheckedCodecShape {}

    /** A primitive written as itself. */
    record Scalar(LeafScalar kind) implements Bare {}

    /** A named data, read and written by its own derived codec. */
    record Named(TypeSymbol name) implements Bare {}

    /** A {@code List<T>}, written as an array. */
    record ListOf(CheckedCodecShape element) implements Bare {}

    /** A {@code Set<T>}, written as an array in its own members' order. */
    record SetOf(CheckedCodecShape element) implements Bare {}

    /** A {@code Map<K, V>}, written as an object whose keys are {@code key}'s bare text. */
    record MapOf(MapKeyRepresentation key, CheckedCodecShape value) implements Bare {}

    /** An {@code Option<T>}. Where this stands decides how absence is written — a field omits its
     *  key, and an element or a map's value writes {@code null}. */
    record OptionOf(Bare present) implements CheckedCodecShape {}
}
