package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Messages;
import souther.compiler.diag.msg.Message;
import souther.compiler.diag.msg.MessageOrder;
import souther.compiler.diag.msg.ReportMessage;

import java.util.List;
import java.util.Locale;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a page says a line once, and where among the others it says it, is decided by what the
 * line says and never by how a language words it.
 *
 * <p>Held with two statements the catalog words alike in every shipped language: a list, and the
 * parts of one thing. A page that told lines apart by their words would say one of them and drop
 * the other, and a rewording that made two entries read alike would change how many lines a reader
 * is given. The words are asserted alike first, so the test is about the case it says it is about.
 */
class WhatALineSaysDecidesWhetherItIsSaidAgainTest {

    private static final Message A_LIST = new ReportMessage.Listed(
            new ReportMessage.Verbatim("a"), new ReportMessage.Verbatim("b"));

    private static final Message PARTS_OF_ONE = new ReportMessage.PartsOfOne(
            new ReportMessage.Verbatim("a"), new ReportMessage.Verbatim("b"));

    @Test
    void twoStatementsWordedAlikeAreTwoLines() {
        for (Locale language : List.of(Locale.ENGLISH, Locale.JAPANESE)) {
            assertEquals(Messages.render(A_LIST, language), Messages.render(PARTS_OF_ONE, language),
                    "the two statements read alike in " + language);
        }

        Set<AdequacyReport.Said> said = new TreeSet<>(AdequacyReport.Said.IN_ORDER);
        said.add(new AdequacyReport.Said(5, 0, A_LIST));
        said.add(new AdequacyReport.Said(5, 0, PARTS_OF_ONE));
        assertEquals(2, said.size(), "two answers in one place, worded alike, are two answers");

        AdequacyReport.Said both = AdequacyReport.everyReason(List.of(
                new AdequacyReport.Said(5, 0, A_LIST), new AdequacyReport.Said(5, 0, PARTS_OF_ONE)));
        assertNotEquals(A_LIST, both.said(), "and a place's two reasons are both said");
    }

    /** And the same statement saying the same thing is one line, however often it is made. */
    @Test
    void oneStatementMadeTwiceIsOneLine() {
        Set<AdequacyReport.Said> said = new TreeSet<>(AdequacyReport.Said.IN_ORDER);
        said.add(new AdequacyReport.Said(5, 0, A_LIST));
        said.add(new AdequacyReport.Said(5, 0, new ReportMessage.Listed(
                new ReportMessage.Verbatim("a"), new ReportMessage.Verbatim("b"))));
        assertEquals(1, said.size());
    }

    /**
     * The order is an order over the messages: equal exactly where they are equal values, and the
     * same between two messages whichever is asked first.
     */
    @Test
    void theOrderIsOverWhatIsSaid() {
        List<Message> each = List.of(A_LIST, PARTS_OF_ONE,
                new ReportMessage.Listed(new ReportMessage.Verbatim("a"),
                        new ReportMessage.Verbatim("c")),
                new ReportMessage.Verbatim("a"), new ReportMessage.Nothing(),
                new ReportMessage.LeftOpen(2), new ReportMessage.LeftOpen(10));
        for (Message one : each) {
            for (Message other : each) {
                int forth = MessageOrder.OF_WHAT_IS_SAID.compare(one, other);
                int back = MessageOrder.OF_WHAT_IS_SAID.compare(other, one);
                assertEquals(one.equals(other), forth == 0, () -> one + " against " + other);
                assertEquals(Integer.signum(forth), -Integer.signum(back),
                        () -> one + " against " + other);
            }
        }
        assertTrue(MessageOrder.OF_WHAT_IS_SAID.compare(new ReportMessage.LeftOpen(2),
                new ReportMessage.LeftOpen(10)) < 0, "a number is ordered as a number");
    }
}
