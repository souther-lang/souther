package souther.compiler.flow;

import java.util.Collections;
import java.util.EnumSet;
import java.util.Set;

/**
 * What a body does at one position: whether a run arrives at a value there, and what it comes to.
 *
 * <p>Said in no words the numbering has, and that is the point of it. This is the reading with no
 * naming behind it, and every reader asking what the body does is answered from it — so a naming
 * cannot move the answer, because the answer was never computed with one.
 *
 * <p>Empty means no run arrives. {@link Truth#UNREAD} standing in here means a run arrives and this
 * reading did not work out which value it came to; it does not mean both, and nothing widens it into
 * both.
 */
public record Comes(Set<Truth> truths) {

    public Comes {
        truths = truths.isEmpty() ? Set.of()
                : Collections.unmodifiableSet(EnumSet.copyOf(truths));
    }

    /** No run arrives at a value here. */
    public static final Comes NOWHERE = new Comes(Set.of());

    /** Whether a run can arrive at a value. */
    public boolean arrives() {
        return !truths.isEmpty();
    }

    /**
     * Whether this reading can say a run never comes out {@code want} here.
     *
     * <p>The question an arm of a fork is there for, and not the question of what the value is. An
     * arm stands unless the reading worked out that the condition never comes out its way, so a value
     * whose truth is unread leaves both arms standing — which is this reading having nothing to say
     * about them and is why the answer is not spelled as a truth.
     */
    public boolean mayCome(boolean want) {
        return truths.contains(Truth.UNREAD) || truths.contains(Truth.of(want));
    }

    /** The values this reading worked out, which is what it will be held to. */
    public Set<Truth> known() {
        Set<Truth> out = EnumSet.noneOf(Truth.class);
        truths.stream().filter(each -> each != Truth.UNREAD).forEach(out::add);
        return Collections.unmodifiableSet(out);
    }
}
