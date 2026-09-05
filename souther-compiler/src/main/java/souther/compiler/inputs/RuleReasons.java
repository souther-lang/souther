package souther.compiler.inputs;

import souther.compiler.diag.Placement;
import souther.compiler.diag.SourcePos;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * What the parts of a rule left a question standing on, and whether that is an order anybody wrote.
 *
 * <p>The one place the claim is made. A reason stands at a place somebody wrote, and reasons written
 * in one text stand in the order that text puts them in; reasons written in two texts stand in no
 * order at all, because nothing an author did says which file comes first. Both of those are
 * answers, and a carrier with only the first would have to make the second up.
 *
 * <p><b>Where the places are still in hand.</b> Downstream of here the reasons are words, and a word
 * says nothing about where it was written — which is how an order arrived at by walking came to be
 * published as the author's and was right about it only while one walk produced every member. So
 * the claim is made here, out of the places, and everything after carries what was decided rather
 * than deciding again.
 */
public sealed interface RuleReasons {

    /** What is held, as the words a reader asks for. */
    List<BlockReason.RuleReadingStopped> reasons();

    /** Whether the question stands on nothing its rule left. */
    default boolean isEmpty() {
        return reasons().isEmpty();
    }

    /**
     * Reasons of one text, in the order the places they stand on were written.
     *
     * <p>An order of the model, which is what {@link AuthoredOrder} means and is why it is the
     * thing held rather than a list beside a flag.
     */
    record AsWritten(AuthoredOrder<BlockReason.RuleReadingStopped> order) implements RuleReasons {

        public AsWritten {
            if (order == null) {
                throw new IllegalArgumentException("an authored order is some order");
            }
        }

        @Override
        public List<BlockReason.RuleReadingStopped> reasons() {
            return order.written();
        }
    }

    /**
     * Reasons written across more than one text, which no order of anybody's runs across.
     *
     * <p>Steady, so that one compiler over one source says the same thing twice; and steady is all
     * it is. What settles it is not a fact about the model, so nothing may be read off it — a reader
     * acting on this order is acting on which text this compiler compared first.
     */
    record NoSingleAuthoredOrder(List<BlockReason.RuleReadingStopped> reasons)
            implements RuleReasons {

        public NoSingleAuthoredOrder {
            reasons = List.copyOf(reasons);
        }
    }

    /**
     * One reason and the place it stands on.
     *
     * @param writtenAt where the part that raised it was written
     * @param reason what it left, in the vocabulary a question stands on
     */
    record Placed(SourcePos writtenAt, BlockReason.RuleReadingStopped reason) {

        public Placed {
            if (writtenAt == null || reason == null) {
                throw new IllegalArgumentException("a reason stands on a place, and says which");
            }
        }
    }

    /**
     * These, in the order they were written where that is an order.
     *
     * <p>Sorted by the place first and folded second, which is what makes the entry the earliest
     * place a reason stands on rather than the first the walk met. Two places in one text are told
     * apart by the line and the column; two reasons at one place are told apart by nothing an author
     * wrote, so they are put in the order the vocabulary declares them in — a canonical order and
     * not a claim about the source, taken from the type so that a word added to it is placed by
     * being added.
     */
    static RuleReasons from(List<Placed> these) {
        if (these.isEmpty()) {
            return new AsWritten(AuthoredOrder.asWritten(List.of()));
        }
        List<Placed> sorted = new ArrayList<>(these);
        sorted.sort(Comparator.comparingInt((Placed each) -> each.writtenAt().line())
                .thenComparingInt(each -> each.writtenAt().column())
                .thenComparingInt(each -> canonical(each.reason())));
        List<BlockReason.RuleReadingStopped> out = new ArrayList<>();
        for (Placed each : sorted) {
            if (!out.contains(each.reason())) {
                out.add(each.reason());
            }
        }
        return texts(these).size() == 1
                ? new AsWritten(AuthoredOrder.asWritten(out))
                : new NoSingleAuthoredOrder(out);
    }

    /**
     * One reason, which is in the order it was written by there being nothing to order it against.
     *
     * <p>Here so that {@link AuthoredOrder} is made in this file and nowhere else. A caller holding
     * one reason and reaching for the order itself would be a second place saying what an authored
     * order is, and the next caller to reach for it would have two examples to follow.
     */
    static RuleReasons one(BlockReason.RuleReadingStopped reason) {
        return new AsWritten(AuthoredOrder.asWritten(List.of(reason)));
    }

    /** None, which is what a question standing on its position's answer alone has here. */
    static RuleReasons none() {
        return new AsWritten(AuthoredOrder.asWritten(List.of()));
    }

    /** Which texts these were written in, since a line and a column are a place only within one. */
    private static Set<Placement> texts(List<Placed> these) {
        Set<Placement> out = new LinkedHashSet<>();
        these.forEach(each -> out.add(each.writtenAt().placement()));
        return out;
    }

    /** Where the vocabulary declares this reason, which is the order two at one place are put in. */
    private static int canonical(BlockReason.RuleReadingStopped reason) {
        Class<?>[] declared = BlockReason.RuleReadingStopped.class.getPermittedSubclasses();
        for (int i = 0; i < declared.length; i++) {
            if (declared[i] == reason.getClass()) {
                return i;
            }
        }
        return declared.length;
    }
}
