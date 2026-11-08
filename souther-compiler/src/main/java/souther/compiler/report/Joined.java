package souther.compiler.report;

import souther.compiler.diag.msg.Message;
import souther.compiler.diag.msg.ReportMessage;

import java.util.List;
import java.util.function.BinaryOperator;

/**
 * Several things a line says, joined into one message the way a page joins them.
 *
 * <p>Joined as messages and not as the text of each, so that what the line says is still a value
 * when it is told apart from another and put in order ({@link AdequacyReport.Said}), and is worded
 * once, by the page that writes it. Nothing where there is nothing to join.
 */
final class Joined {

    private Joined() {
    }

    /** {@code a, b, c}. */
    static Message listed(List<? extends Message> each) {
        return joined(each, (first, rest) -> new ReportMessage.Listed(first, rest));
    }

    /** {@code a and b and c}. */
    static Message both(List<? extends Message> each) {
        return joined(each, (first, rest) -> new ReportMessage.Both(first, rest));
    }

    /** {@code a; b; c}: reasons said one after another. */
    static Message reasons(List<? extends Message> each) {
        return joined(each, (first, rest) -> new ReportMessage.Reasons(first, rest));
    }

    /** {@code a, and b}: one thing said, and another true beside it. */
    static Message also(List<? extends Message> each) {
        return joined(each, (first, rest) -> new ReportMessage.Also(first, rest));
    }

    /** {@code a or b or c}. */
    static Message either(List<? extends Message> each) {
        return joined(each, (first, rest) -> new ReportMessage.Either(first, rest));
    }

    /** The same of text that is already words or code, each said as it stands. */
    static List<Message> asWritten(List<String> each) {
        return each.stream().<Message>map(ReportMessage.Verbatim::new).toList();
    }

    private static Message joined(List<? extends Message> each, BinaryOperator<Message> join) {
        if (each.isEmpty()) {
            return new ReportMessage.Nothing();
        }
        Message said = each.getLast();
        for (int i = each.size() - 2; i >= 0; i--) {
            said = join.apply(each.get(i), said);
        }
        return said;
    }
}
