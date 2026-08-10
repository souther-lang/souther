package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A comment stands in one of three positions relative to what it is about, and which one is read
 * from the line breaks around it — the blank line included, not only whether a line ended.
 *
 * <p>The three are held together here rather than one to a test, because the answer for each is
 * what rules the other two out. Reading only whether a line ended leaves two of the three sharing
 * an answer, and a note written under a declaration comes back describing the next one — a change
 * of what the comment is about rather than of where it is written, so a test comparing the text of
 * one of these cases alone would let it through.
 */
class WhatACommentIsAboutIsReadFromTheBreaksAroundItTest {

    @Test
    void onTheCodesOwnLineItIsAboutThatCode() {
        assertEquals("""
                module m

                data OwnCost = Reimbursement | Advance // the cases are units

                behavior quote : (c: Cart) -> PricedCart
                """, Formatter.format("""
                module m
                data OwnCost = Reimbursement | Advance // the cases are units

                behavior quote : (c: Cart) -> PricedCart
                """));
    }

    @Test
    void runningIntoWhatFollowsItIsAboutWhatFollows() {
        assertEquals("""
                module m

                data OwnCost = Reimbursement | Advance
                // what quote does
                behavior quote : (c: Cart) -> PricedCart
                """, Formatter.format("""
                module m
                data OwnCost = Reimbursement | Advance
                // what quote does
                behavior quote : (c: Cart) -> PricedCart
                """));
    }

    @Test
    void cutOffFromWhatFollowsItIsAboutWhatIsAboveIt() {
        assertEquals("""
                module m

                data OwnCost = Reimbursement | Advance
                // the cases are units; nothing else declares them

                behavior quote : (c: Cart) -> PricedCart
                """, Formatter.format("""
                module m
                data OwnCost = Reimbursement | Advance
                // the cases are units; nothing else declares them

                behavior quote : (c: Cart) -> PricedCart
                """));
    }

    /**
     * A blank line above the comment as well as below it puts nothing between it and what follows
     * that is not also between it and what came before, so it stays what it was: about what follows.
     */
    @Test
    void cutOffFromBothItIsAboutWhatFollows() {
        assertEquals("""
                module m

                data OwnCost = Reimbursement | Advance

                // what quote does
                behavior quote : (c: Cart) -> PricedCart
                """, Formatter.format("""
                module m
                data OwnCost = Reimbursement | Advance

                // what quote does

                behavior quote : (c: Cart) -> PricedCart
                """));
    }

    /**
     * A run of comment lines is one comment for this question. Answered line by line, the last line
     * of a run with a blank under it would go to one owner and every line above it to the other.
     */
    @Test
    void aRunOfLinesIsAboutOneThing() {
        assertEquals("""
                module m

                data OwnCost = Reimbursement | Advance
                // the cases are units
                // nothing else declares them

                behavior quote : (c: Cart) -> PricedCart
                """, Formatter.format("""
                module m
                data OwnCost = Reimbursement | Advance
                // the cases are units
                // nothing else declares them

                behavior quote : (c: Cart) -> PricedCart
                """));
    }

    /**
     * With nothing after it there is no member for a blank line to separate the comment from, which
     * is what the fourth carrier answers and not this question. It closes the file.
     */
    @Test
    void withNothingAfterItItClosesTheFile() {
        assertEquals("""
                module m

                data OwnCost = Reimbursement | Advance
                // the cases are units
                """, Formatter.format("""
                module m
                data OwnCost = Reimbursement | Advance
                // the cases are units
                """));
    }

    /** Reading it back gives the same answer, so the position the canonical form writes a comment
     *  in is one the canonical form reads as that position. */
    @Test
    void eachAnswerIsWrittenInTheFormThatIsReadBackAsIt() {
        for (String source : new String[] {
                """
                module m
                data OwnCost = Reimbursement | Advance // the cases are units

                behavior quote : (c: Cart) -> PricedCart
                """,
                """
                module m
                data OwnCost = Reimbursement | Advance
                // what quote does
                behavior quote : (c: Cart) -> PricedCart
                """,
                """
                module m
                data OwnCost = Reimbursement | Advance
                // the cases are units

                behavior quote : (c: Cart) -> PricedCart
                """}) {
            String once = Formatter.format(source);
            assertEquals(once, Formatter.format(once), once);
        }
    }
}
