package souther.compiler.diag.msg;

import souther.compiler.diag.Localizable;

import java.util.Comparator;
import java.util.Map;

/**
 * An order over what messages say, read off the messages and never off how a language words them.
 *
 * <p>What a page says once, and in which order among lines of one kind, is a question about what
 * each line says. Asked of the words instead, a translation, or a catalog entry reworded in the
 * base language, changes which lines a reader is given: two statements a rewording happens to word
 * alike are said once, and the order of the rest moves with the spelling.
 *
 * <p>So two messages are ordered first by which statement they are — the catalog entry, which is
 * the statement's name and not its wording — and then by what they carry, component by component in
 * the order the message declares them: text and numbers as they are, and a message carried as a
 * value by this same order. Two messages are equal under it exactly where they are equal values, so
 * a set ordered by it holds one entry per thing said.
 */
public final class MessageOrder {

    private MessageOrder() {
    }

    /** Which statement, then what it carries. */
    public static final Comparator<Message> OF_WHAT_IS_SAID = MessageOrder::compare;

    private static int compare(Message one, Message other) {
        if (one == other) {
            return 0;
        }
        int which = MessageKeys.of(one).compareTo(MessageKeys.of(other));
        if (which != 0) {
            return which;
        }
        Map<String, Object> mine = MessageValues.of(one);
        Map<String, Object> theirs = MessageValues.of(other);
        for (Map.Entry<String, Object> each : mine.entrySet()) {
            int by = value(each.getValue(), theirs.get(each.getKey()));
            if (by != 0) {
                return by;
            }
        }
        return 0;
    }

    private static int value(Object one, Object other) {
        if (one == null || other == null) {
            return one == null ? (other == null ? 0 : -1) : 1;
        }
        return switch (one) {
            case Message m when other instanceof Message o -> compare(m, o);
            case String s when other instanceof String o -> s.compareTo(o);
            case Integer i when other instanceof Integer o -> Integer.compare(i, o);
            case Long l when other instanceof Long o -> Long.compare(l, o);
            case Localizable l when other instanceof Localizable o -> localizable(l, o);
            default -> throw new IllegalArgumentException("a message carries text, numbers and"
                    + " messages, and this one carries " + one.getClass().getName() + " and "
                    + other.getClass().getName() + " in one place");
        };
    }

    private static int localizable(Localizable one, Localizable other) {
        int key = one.key().compareTo(other.key());
        if (key != 0) {
            return key;
        }
        Object[] mine = one.args();
        Object[] theirs = other.args();
        for (int i = 0; i < Math.min(mine.length, theirs.length); i++) {
            int by = value(mine[i], theirs[i]);
            if (by != 0) {
                return by;
            }
        }
        return Integer.compare(mine.length, theirs.length);
    }
}
