package souther.compiler.types;

import souther.compiler.diag.SourcePos;

/**
 * What a written type comes to: the type it stands for, or the one member of it no arm can name.
 *
 * <p>Two answers because the reading has two, and the second is not an absence of the first. A
 * written type one of whose members cannot be a member is a mistake an author owns, and what a
 * reader does about it is report it. Carried as a value so that reading and reporting are not the
 * same act: the reading belongs to the written type and is done once, where it is built; reporting
 * belongs to whoever asks.
 *
 * <p>A member no arm can name may be written inside a function type, so the second answer names the
 * type written and where it stands rather than the whole that was asked about. It travels out
 * through the function type that read it, which is how what a reader reports stays the thing an
 * author wrote it at.
 *
 * <p>Beside the type rather than beside the tree, being what the front end settled about a written
 * type rather than a form the grammar has.
 */
public sealed interface WrittenTypeMeaning extends SettledAnswer {

    /** The type this written type stands for. */
    record Settled(Type type) implements WrittenTypeMeaning {}

    /** A member no arm can name, and where it was written. */
    record NotAMember(Type member, SourcePos at) implements WrittenTypeMeaning {}
}
