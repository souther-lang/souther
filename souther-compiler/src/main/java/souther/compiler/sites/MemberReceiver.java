package souther.compiler.sites;

import souther.compiler.diag.Region;

/**
 * What the left of a {@code .} turned out to be.
 *
 * <p>Asked about the access and not about the receiver, because the receiver is not always something
 * the source wrote an occurrence of. {@code request.plannedCost} is one — a value, taken apart by
 * the field read around it. {@code m} in {@code m.name} is not: where the qualifier names a module,
 * resolution answers the whole chain as one name, and there is no node under it to ask about. The
 * parser cannot tell the two apart at all, since both are written the same way, and what settles it
 * is a binding being in force.
 *
 * <p>So the question is put at the access, and the answer says which of them it was. An editor
 * offering what may be written after a {@code .} reads the answer and offers the fields of a type or
 * the names of a namespace, and it never has to work out which of the two it is looking at.
 *
 * <p>Absence is a third answer and is not one of these: no access was written there. A receiver that
 * is a value and has no type to show is {@link UntypedValue}, which is a receiver, and the two are
 * different things to offer nothing for.
 */
public sealed interface MemberReceiver {

    /**
     * The characters the receiver is written over.
     *
     * <p>Carried because it is not the access's own, and a caller that has to know how far into the
     * source an answer reaches cannot work it out from the access: an access runs to the end of the
     * member name, and a receiver stops at the {@code .}. A reader answering about a source it has
     * finished off for the author is exactly that caller — what it may use is what was written
     * before it put anything in, and the receiver is, while the access around it is not.
     *
     * <p>Where the receiver is a namespace it is the qualifier, which is written and has no
     * occurrence of its own; where it is a value it is that value's occurrence.
     */
    Region writtenAt();

    /** A value, and what it is. */
    record Value(TypeFact type, Region writtenAt) implements MemberReceiver {}

    /**
     * A value, and nothing a declaration says about what type it has.
     *
     * <p>What is missing is evidence rather than the receiver: it is a value, and this reading of
     * the declarations did not reach a type for it — a call's answer, a name declared elsewhere with
     * a body this does not read.
     */
    record UntypedValue(Region writtenAt) implements MemberReceiver {}

    /**
     * A namespace, reached by the qualifier the author wrote.
     *
     * <p>Two of them, because they are reached from different places and a reader offering what is
     * inside one goes to a different place for each. Which one it is is settled here rather than
     * carried as a spelling for a reader to resolve again: a spelling is what the author typed, an
     * alias among other things, and resolving it twice is two answers about what {@code m} is.
     */
    sealed interface Namespace extends MemberReceiver {

        /** A module of this compilation, under its own name — never the alias an import gave it. */
        record OfModule(String module, Region writtenAt) implements Namespace {}

        /** One of the qualifiers the language reserves, which name no module of this compilation. */
        record OfLibrary(String qualifier, Region writtenAt) implements Namespace {}
    }
}
