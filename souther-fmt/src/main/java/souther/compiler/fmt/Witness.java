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
     */
    record Indentation(Levels unit, int canonical, int source) implements Witness {}

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
}
