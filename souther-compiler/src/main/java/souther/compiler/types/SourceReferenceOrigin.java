package souther.compiler.types;

/**
 * Which reference the source wrote, said in a way that respelling and copying cannot change.
 *
 * <p>One question and only one: <em>which occurrence of a name did the author write?</em> Not what
 * the name reaches — two references to one declaration reach the same thing and are two references
 * ({@link ReachName}) — and not how it is spelled, because a pass may respell one: a helper written
 * bare in the module that declares it is written qualified in a body carried out of that module, and
 * it is the same reference the author wrote.
 *
 * <p><b>Why neither of those could stand in.</b> A route is what a reference means, so two
 * occurrences of one name are one route; a spelling is what a pass may replace, and
 * {@code WrittenName.authored} answers whether the spelling is the author's rather than whether the
 * reference is. A place is where to underline a complaint, which is a different contract that has
 * already parted company with identity elsewhere — a body copied into another module carries the
 * place it was written at. So identity is minted where the source is read and carried from there,
 * which is what {@link SourceConstructOrigin} already does for the constructs a source writes.
 *
 * <p><b>Not a name anything outside one compilation can be matched by.</b> {@code ordinal} is the
 * builder's own count over the source it is reading. What identity needs is that the numbering be a
 * function of the source and that two references never share one, which it is and they do not —
 * matching one compilation's references against another's is a different question and not one this
 * answers.
 *
 * @param module   the module whose source wrote the reference, since each source numbers from zero
 * @param ordinal  which reference of that source it is, by the builder's own count over it
 */
public record SourceReferenceOrigin(String module, int ordinal) {

    public SourceReferenceOrigin {
        if (module == null) {
            throw new IllegalArgumentException("a reference the source wrote is in some module");
        }
        if (ordinal < 0) {
            throw new IllegalArgumentException(
                    "a reference is counted from zero: " + ordinal);
        }
    }

    @Override
    public String toString() {
        return module + "#ref" + ordinal;
    }
}
