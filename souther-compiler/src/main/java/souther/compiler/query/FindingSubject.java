package souther.compiler.query;

import souther.compiler.types.TypeSymbol;

/**
 * What a finding is about, which is not always a behavior.
 *
 * <p>Two things a model is short of and they are not one. A {@code match} arm nothing reaches and a
 * case no row expects are facts about a body: they are found by reading one behavior, and the author
 * fixes them by writing a row for that behavior. A line an {@code invariant} drew is a fact about
 * the type: whether a row standing at the boundary of {@code UserId} is believed is a question about
 * {@code UserId}, and the answer cannot differ between the behaviors carrying it (issue #1062).
 *
 * <p><b>Because there is no behavior to name.</b> Findings used to be a behavior and a list, so a
 * finding about a declaration had to be filed under one of the behaviors that carry it — the first
 * one a walk reached, which is a choice nothing made and a reader cannot check. An author sent to
 * {@code scheduleMeeting} to fix what {@code UserId} says would be sent to a body that says nothing
 * about the length of a user id.
 *
 * <p>Grouping is a reader's, and it is not this. A report prints a block per behavior because that
 * is how somebody reads it; the model says what each finding is about and lets whoever is printing
 * decide what to put beside what. Held as the key of a map, the two were one and the presentation
 * won.
 */
public sealed interface FindingSubject {

    /** What a report calls it, in English, the way every other word this writes is chosen. */
    String named();

    /** A body of the module: what a row written for that behavior answers. */
    record OfABehavior(String name) implements FindingSubject {

        public OfABehavior {
            if (name == null) {
                throw new IllegalArgumentException("a finding about a behavior says which");
            }
        }

        @Override
        public String named() {
            return name;
        }
    }

    /**
     * The declarations of the module that owe the line: what their own rules say, wherever the type
     * is carried.
     *
     * <p>The declaration and not the clause. Which rule of it a finding is about is the finding's
     * own ({@link About}), and a subject that carried the clause would be two answers about one
     * question — what a report prints this under is the declaration either way.
     *
     * <p><b>Several, and one finding.</b> A bound an inner record and an outer record both take in
     * at one value is one line and one row to write, and each of them is one where taking it away
     * leaves the end where it is — so there is no one of them to file this under, and choosing would
     * name a declaration as the answer when the reading does not know which is
     * ({@link souther.compiler.partition.AuthoredLine#obligationOwners}). Every owner and not one of
     * them, because the work is theirs together.
     *
     * <p>Of this module. An owner written in another module owes the line there and is not what an
     * author reading this report can change; the line is still one the values here are held to, and
     * what says so is the block about the behavior carrying it.
     */
    record OfADeclaration(java.util.List<TypeSymbol.AtModule> declarations)
            implements FindingSubject {

        public OfADeclaration {
            declarations = java.util.List.copyOf(declarations);
            if (declarations.isEmpty()) {
                throw new IllegalArgumentException("a finding about a declaration says which");
            }
        }

        /** One of them, for a reader with room for one word. */
        public OfADeclaration(TypeSymbol.AtModule declaration) {
            this(java.util.List.of(declaration));
        }

        /**
         * What a report calls them.
         *
         * <p>The same join the line's own name uses for the declarations that took an end in
         * ({@link souther.compiler.partition.AuthoredLine#said}), because it is the same set of
         * declarations being said — a second spelling of one list reads as two.
         */
        @Override
        public String named() {
            return declarations.stream().map(TypeSymbol::name)
                    .collect(java.util.stream.Collectors.joining(" or "));
        }
    }

    /** Whether this is the behavior named {@code name}, for a reader printing a block per behavior. */
    default boolean isBehavior(String name) {
        return this instanceof OfABehavior it && it.name().equals(name);
    }
}
