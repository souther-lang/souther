package souther.compiler.fmt;

import souther.compiler.cst.SyntaxKind;

/**
 * A rule, one of its units, what the canonical form has there and what the source has instead.
 *
 * <p>One per rule rather than one shape for all of them. The structure is common — which rule, which
 * unit, the two answers — and the answers are not: a spacing expectation and an indentation
 * expectation share nothing but their place in the record.
 *
 * <p>A witness is not a difference in the text. One record literal written down the page changes
 * every member boundary under it, and the rule that decided answers about the group; a witness per
 * changed boundary would be counting the text and calling the count decisions. So the unit is the
 * rule's, and the differences that came from it are one witness.
 *
 * <p>And a witness owns no patch. Two of them routinely land on the same line of the canonical form,
 * so the text they add up to is composed once from the expectations rather than edit by edit.
 */
sealed interface Witness {

    /**
     * The indentation rule's unit: a level of nesting and the one it is written inside.
     *
     * <p>A pair, because what the rule says is that the inner is one indent further in than the
     * outer. A unit of one level would have to name a number the rule never states — a formatter
     * indenting the first level by four and the second by six writes the same eight at depth two.
     *
     * <p>{@code outer} is null for the outermost level, whose line the file holds at column zero.
     */
    record Levels(Doc.NestRef outer, Doc.NestRef inner) {}

    /**
     * The indentation rule at one pair of levels: how much further in the canonical form writes the
     * inner one, and how much further in the source wrote it.
     *
     * <p>Both are differences and neither is a column. A source that indents a whole construct by
     * two writes every line inside it in the wrong column, and what it got wrong is one step.
     *
     * <p>The source's is a list because a source need not have been consistent. The rule was
     * evaluated once and says one step; what the source wrote at that unit can be two, and saying
     * so is not two decisions.
     */
    record Indentation(Levels unit, int canonical, java.util.List<Integer> source)
            implements Witness {

        public Indentation {
            source = java.util.List.copyOf(source);
        }
    }

    /**
     * The spacing rule's unit: one boundary of the canonical form, named by which adjacency of its
     * tokens it is and by what the rule was asked about there.
     *
     * <p>An occurrence and not a kind of boundary. One adjacency is one evaluation of this rule —
     * which is what makes it the one family where a difference in the text and a decision are the
     * same count — so two boundaries the rule answers the same way are two units.
     */
    record Boundary(int adjacency, SyntaxKind joining, SyntaxKind left, SyntaxKind right) {}

    /**
     * The spacing rule at one boundary: what the canonical form writes between the two tokens, and
     * what the source wrote there.
     *
     * <p>Only where the canonical form writes both of them on one line. Where it breaks the
     * boundary there is no spacing it writes, and a witness saying the source's space is wrong
     * would be telling an author to change a space that should be a line break.
     */
    record BetweenTwoTokens(Boundary unit, String canonical, String source) implements Witness {}

    /**
     * The separation rule's unit: two top-level items, one written after the other.
     *
     * <p>A pair, because what the rule says is what stands between them. A blank line is two breaks
     * at one adjacency and the rule did not answer twice, so a witness per break would be counting
     * the newlines the layout wrote.
     */
    record Items(Place previous, Place next) {}

    /**
     * The separation rule at one pair of items: how many blank lines the canonical form writes
     * between them, and how many the source wrote.
     */
    record Separation(Items unit, int canonical, int source) implements Witness {}

    /**
     * The conditional-layout rule's unit: one group, and where in the canonical form it stands.
     *
     * <p>The group and not the boundaries under it. One record literal written down the page moves
     * every member boundary it holds, and the rule was evaluated once — whether the line this would
     * take is within the width.
     */
    record Group(Doc.GroupRef group, int at) {}

    /**
     * The conditional-layout rule at one group: whether the canonical form writes it on one line,
     * and whether the source did.
     *
     * <p>Only for a group the width decided. One written down the page because it holds something
     * that cannot be laid out flat was settled before this rule was asked, and the forced-layout
     * rule is what answers for it.
     */
    record Conditional(Group unit, boolean canonicalIsWhole, boolean sourceIsWhole)
            implements Witness {}

    /**
     * The comment rules' unit: one comment, named by where the source wrote it.
     *
     * <p>The comment and not the line it is on. Where a run of them stands above a definition, each
     * is one the formatter placed, and what stands between two of them is as much a decision as
     * what stands between the last and what they are about.
     */
    record Comment(int at) {}

    /**
     * A comment written at the end of a line of code: what the canonical form puts between the code
     * and it, and what the source put there.
     *
     * <p>Only where both write it on that line. A source that put the comment somewhere else has
     * not spaced it wrongly — which construct carries a comment is another question, and one this
     * rule reads the answer to rather than asking.
     */
    record TrailingComment(Comment unit, String canonical, String source) implements Witness {}

    /**
     * A comment written on a line of its own: how many lines end between it and what it is written
     * above, and how many the source left there.
     *
     * <p>A count and not the text. How far in the next line begins is the indentation rule's, and a
     * comment rule that answered with the whole stretch would be answering for it too.
     */
    record CommentAbove(Comment unit, int canonical, int source) implements Witness {}

    /**
     * A comment the canonical form writes somewhere else: which adjacency of the code it stands in
     * there, and which it stands in in the source.
     *
     * <p>Which construct carries a comment is a decision, and it is taken over the places the
     * canonical form has rather than over the source's tree — where the two differ, a comment can
     * only be filed against something that is written. So this says where it went, and the two
     * numbers are adjacencies of the code both texts share.
     */
    record CommentCarrier(Comment unit, int canonical, int source) implements Witness {}

    /**
     * A forced-layout rule's unit: one boundary the canonical form breaks whatever the width, and
     * the obligation it breaks it for.
     *
     * <p>These are the rules whose unit and whose boundary are the same thing. One adjacency of two
     * members is one pair, one bracket is one bracket, one comment is one comment and one file is
     * one file — unlike a group, which holds many boundaries and was decided once, or a pair of
     * nesting levels, which many lines are written under.
     *
     * <p>{@code adjacency} is which pair of the canonical form's tokens it stands between, and
     * {@code -1} the end of the file, where there is no token after it.
     */
    record ForcedBoundary(int adjacency, Obligation obligation) {}

    /**
     * A forced-layout rule at one boundary: how many lines the canonical form ends there, and how
     * many the source ends.
     *
     * <p>A count and not whether a line ends. A construct writes its members one to a line, so a
     * source that left a blank line between two of them has as much departed from that as one that
     * ran them together — and a witness that said only that the source does not end a line there
     * would be saying something untrue of the first.
     */
    record Forced(ForcedBoundary unit, int canonical, int source) implements Witness {}
}
