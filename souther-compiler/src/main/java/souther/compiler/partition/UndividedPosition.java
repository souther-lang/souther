package souther.compiler.partition;

import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.TermPath;

/**
 * A position no class came back for, and which of the three ways that happened.
 *
 * <p>The list of these used to be a list of paths, and everything downstream read a path in it as the
 * model having no distinction to draw there. A position whose rule is written in a form this does not
 * read is in that same list, and saying the same sentence about both tells an author to stop looking
 * for the line their own body draws.
 *
 * <p>So the absence is a value that has to be produced rather than the default reading of an empty
 * result. {@link Why.Absent} is produced by {@link PendingPosition#complete} and nowhere else, from
 * a position whose structural reading did not stop and whose rules were all read and drew nothing —
 * which is what the word means.
 *
 * <p>The other two are the two ways of not being that, and they are opposite sentences about this
 * compiler. Where a reading stopped, {@link Why.CannotDerive} says something is written here that
 * this did not read. Where every reading ran to the end and a rule states something that draws no
 * line — a relation between two positions, a quantity the position cancels out of —
 * {@link Why.StatedWithoutALine} says that instead: nothing is missing, and a reader sent after a
 * limit would be looking for one that is not there. Held as one, the second went out as the first.
 *
 * @param at  the position, spelled the way a report names it
 * @param why whether the model draws nothing here, this could not read what it draws, or a rule
 *            read from end to end states something that is no line
 */
public record UndividedPosition(TermPath at, Why why) {

    /** Which of the three it is. */
    public sealed interface Why {

        /**
         * Every reading ran to the end, none of them stopped, and none of them divided the
         * position: the model divides it no way at all.
         *
         * <p>A class with no way to make one rather than a record, because what it says is a
         * conclusion about a model and the only thing entitled to draw it is the completion of a
         * {@link PendingPosition}. Anything able to write {@code new Absent()} is able to say the
         * model divides a position no way without having asked anything, which is the sentence this
         * whole protocol exists to stop being cheap to write.
         */
        final class Absent implements Why {

            /** The one, reached through {@link PendingPosition#complete}. */
            static final Absent PROVEN = new Absent();

            private Absent() {}

            @Override
            public boolean equals(Object other) {
                return other instanceof Absent;
            }

            @Override
            public int hashCode() {
                return Absent.class.hashCode();
            }

            @Override
            public String toString() {
                return "Absent";
            }
        }

        /**
         * Something is written here that this did not read, so nothing is established either way.
         *
         * <p>What stopped it is not here. A verdict says whether anything divides the position; the
         * findings beside it say what was not read and by whose account, and each of those is made
         * by the reader that has the fact — with the rule where there is one. Carried here too, a
         * report read the cause back off the verdict, which is where the rule had already been
         * lost.
         */
        record CannotDerive() implements Why {}

        /**
         * Every reading ran to the end, and a rule states something here that draws no line.
         *
         * <p>Neither of the two above. Not an absence — the model states something at this position,
         * and a verdict saying it divides the position no way would deny the declaration two tokens
         * away. Not a derivation this compiler could not make either: nothing was missing, and a
         * reader sent after a limit would be looking for one that is not there.
         *
         * <p>What states it is named in a finding of its own, with the rule. Nothing here carries
         * the rule, for the reason {@link CannotDerive} carries no cause: a verdict says whether
         * anything divides the position, and reading a cause back off a verdict is where the rule
         * was lost.
         */
        record StatedWithoutALine() implements Why {}
    }

    /**
     * What stopped the derivation, in the words a document is written in.
     *
     * <p>Each of these is a fact about this compiler, said at the coarseness a reader of a document
     * is promised. They are told apart because they are lifted by different work: one wants a
     * reader for a form of condition, one wants the walk to go deeper, and a report that named
     * neither could not say which.
     *
     * <p>Not the cause itself. What a producer recorded is a {@link BlockReason}, and one of these
     * is what {@link ReportedReason} projects it to — three missing traversals arrive here as one
     * word. So a reader of this knows which kind of thing stopped the derivation and not which
     * capability was missing.
     */
    public enum Reason {
        /**
         * A rule about this position was read and could not be used.
         *
         * <p>Said of the rule and not of one way of failing to use it. A comparison inside a
         * condition this does not take apart is one; a rule naming which values may stand here,
         * written as something other than a value written out, is another. Which reader of the
         * clause gave up is not part of the promise.
         *
         * <p>A rule this never arrived at is {@link #RULES_NOT_READ_AT_ALL} and not this. The two
         * were one word, and the sentence this one prints — an expression the terms do not name —
         * was said of positions whose rules nothing had looked at, which is a different thing and
         * is lifted by different work.
         */
        UNSUPPORTED_SYNTAX,
        /**
         * The reading did not reach the rules written about this position.
         *
         * <p>Nothing here was read and found wanting: the rules are behind something this walk did
         * not enter, and what is written under it is whatever it is. Which limit stopped the walk
         * is not recorded and is not promised — a depth, a type it had been through, a shape it
         * does not descend into, and a clause that could not be typed all leave the same hole, and
         * a reader is told the hole and not this compiler's route to it.
         */
        RULES_NOT_READ_AT_ALL,
        /**
         * The rule was reached, and nothing worked out what it says about the values here.
         *
         * <p>Between the two above, and neither of them. {@link #UNSUPPORTED_SYNTAX} says a rule
         * was read and could not be used — something engaged with it and gave up, and what a
         * reader may go on to do about it is find the form it is written in. {@link
         * #RULES_NOT_READ_AT_ALL} says the rule was never arrived at, and what is written under
         * that hole is whatever it is. This one is a rule that arrived and that nothing here
         * established an interpretation of for the question it raises.
         *
         * <p>Nothing is claimed about which capability would make it interpretable. That is what
         * separates it from the first: an author sent after a form to rewrite would be looking for
         * one nothing complained about, and the rule may be perfectly ordinary and read in full
         * somewhere else. What is known is that the rule is here, that a question of it is
         * standing, and that nothing answered it.
         */
        RULE_NOT_INTERPRETED_HERE,
        /** The values the comparison is against are not ones a line can be drawn on here. */
        UNSUPPORTED_DOMAIN,
        /**
         * Two rules of the position are about its two coordinates, and neither can be chosen.
         *
         * <p>Not {@link #UNSUPPORTED_SYNTAX}, which is where a rule was read and could not be
         * used: here both were read and used perfectly well, and what is missing is a rule for
         * which of a position's two coordinates it is measured at. Said as the first, an author was
         * sent looking for a form this compiler reads.
         */
        COMPETING_COORDINATES,
        /**
         * The line reaches positions under the cases each side of it, and which of them go together
         * is not worked out.
         *
         * <p>Not about how many sums are on the way. A name each side of the line stands at more
         * than one position, and whether those positions pair off one for one or every one against
         * every other is a fact about the model — two names narrowed by one value are narrowed
         * together, and two names under separate choices are not. Said as a shape this compiler does
         * not read, an author would go looking for another way to write a comparison it reads
         * perfectly well.
         */
        UNRESOLVED_CASE_PAIRING,
        /**
         * The comparison relates two positions rather than dividing one.
         *
         * <p>`+x < y+` says where one position stands against another, and a class here is a set of
         * values of one position. Nothing is missing from the carrier — both sides are ordered and a
         * line drawn on either against a number would be read — so saying the values cannot carry a
         * line would send a reader after the wrong thing entirely.
         */
        UNSUPPORTED_PARTITION_SHAPE,
        /**
         * The rule draws its line on a number taken over a run of this position's values, so it
         * divides none of them.
         *
         * <p>Its own word and not the shape above. Nothing here is between two positions and
         * nothing is missing: the rule is read, its border is drawn, and the number it is about is
         * what the values at this place come to rather than any one of them. Two of them either
         * side of a total are on the line as surely as one is, so the position has no class this
         * rule drew — and a reader told the rule relates two positions would go looking for a pair
         * that is not there.
         */
        RULE_ABOUT_A_RUN,
        /**
         * The input returns here to a declaration it has already been through, and what is under
         * this position was not read again.
         *
         * <p>A position whose values are values of a type the path has already met. What stands
         * under it is what stands under that one, so a reader is told the return rather than a list
         * of positions repeating for as long as anybody keeps reading.
         */
        RETURNS_TO_A_DECLARATION_ALREADY_READ,
        /**
         * The type at this position could not be interpreted, so nothing about its values is
         * established. A model carrying one compiles, which is why this is a word a report writes
         * rather than a state nothing reaches.
         */
        TYPE_UNRESOLVED,
        /**
         * A rule is written about a value that came from this position rather than about it.
         *
         * <p>The rule was read and where its value came from is known. What it says about the values
         * at this position is not: an operation made them into something else first, and reading the
         * rule back through that is a capability nothing here has.
         *
         * <p>Its own word, so that a reader is not sent after a form this compiler cannot parse.
         * What would lift it is a reading of what a closure does to a value, and not a wider
         * fragment of comparisons.
         */
        RULE_ABOUT_A_DERIVED_VALUE,
        /**
         * A rule naming this position was read to the end and cuts nothing at all: what it compares
         * is a number the position does not appear in.
         *
         * <p>Its own word because nothing is owed on its account. A reader told the spelling
         * defeated this compiler would go looking for a form to rewrite, and the form was read
         * completely — there was no line in the rule to draw.
         */
        RULE_CUTS_NOTHING,
        /**
         * A rule naming this position was read to the end and draws its line where the quantity it
         * cuts never runs: three times a length is never negative, and a rule comparing one against
         * a negative has no value either side of its line.
         *
         * <p>Its own word beside {@link #RULE_CUTS_NOTHING}, which is what a rule with no quantity
         * to cut gets. Both were read completely and neither divides the position, and what a
         * reader may go on to do about them differs: one rule states something about the position
         * that no row can satisfy, and the other states nothing about it at all.
         */
        RULE_CUTS_OUTSIDE_WHAT_THE_QUANTITY_HOLDS,
        /**
         * The position holds its values inside something this does not reach into — the elements of
         * a collection, what an optional holds, what a map holds. One word for all of them: which
         * reaching is missing is a fact about this compiler, and the model reads the same either
         * way. What this compiler could not do is told apart internally
         * ({@link BlockReason.UnsupportedTraversal}).
         */
        UNSUPPORTED_TRAVERSAL
    }

    /**
     * The absence, of a position that has been completed.
     *
     * <p>The argument is the proof. A {@link PendingPosition} is made from a position whose local
     * producers all came back with nothing, and only completing one reaches this — so what cannot
     * happen is an absence written by a reader that did not ask. Outside this package there is
     * neither a way to make one of those nor a name for this.
     */
    static UndividedPosition absentAfter(PendingPosition proven) {
        return new UndividedPosition(proven.at(), Why.Absent.PROVEN);
    }

    static UndividedPosition statedWithoutALine(TermPath at) {
        return new UndividedPosition(at, new Why.StatedWithoutALine());
    }

    static UndividedPosition cannotDerive(TermPath at) {
        return new UndividedPosition(at, new Why.CannotDerive());
    }

    public boolean isAbsent() {
        return why instanceof Why.Absent;
    }
}
