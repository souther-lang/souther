package souther.compiler.numeric;

import souther.compiler.values.InOneOrder;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.function.Function;

/**
 * One order over the positions of an atom domain, for a walk that has to take them in one.
 *
 * <p><b>What a value of that domain is, said as an order.</b> A form is a mapping and holds no order
 * of its own; a reader that walks it to work a bound out at each position, or to say which of them a
 * rule left unbounded, has the order it walked in inside its answer. So two forms that are equal
 * have to hand that reader one walk, and what settles the walk has to be settled by what the
 * positions are.
 *
 * <p><b>Which is why this is not a comparator a value carries.</b> Held inside a form, an order
 * would make one rule two values under two policies; hidden inside one, equal forms would walk two
 * ways under two policies and the reader's answer would be back where it started. It belongs to the
 * atom domain, and it is asked for where the walk is.
 *
 * <p><b>The law, which is one direction and not two.</b> An order here is total, is a function of
 * the two positions it is asked about and of nothing else, and is a coarsening of equality: two
 * positions that are one compare as one. The converse is not promised and is not a thing every
 * domain can promise — what a domain can see of a position may be less than what tells two of them
 * apart, and the honest ones say so. {@link souther.compiler.check.FactSubject} is such a domain: an
 * evaluation is its own subject and two of them are told apart by being that one, which no writing
 * of them carries.
 *
 * <p><b>So the missing direction is established where a walk needs it, and is established there for
 * every walk.</b> Two positions an order cannot tell apart are two positions it would hand over as
 * one — weighing one of them twice and the other never — so a walk refuses the pair rather than
 * choosing between them. That refusal is {@link #walking}, which is what a caller sorts with;
 * written at a caller instead, it would be a rule the next caller has to remember. The same shape is
 * said of a published arrangement by {@code CanonicalArrangement}, which refuses a key that leaves
 * two unequal things tied.
 *
 * <p><b>And read off what equality reads and nothing else.</b> A rendering is written for a person:
 * two positions rendering alike are not one position, which is why an order taken off the renderings
 * is not one of these however well it happens to work today.
 *
 * @param <A> what a position of the domain is
 */
public interface CanonicalOrder<A> extends Comparator<A> {

    /**
     * {@code these}, in this order, with a pair this cannot tell apart refused rather than walked
     * as one.
     *
     * <p><b>Where the direction the law does not promise is established.</b> An order is a
     * coarsening of equality and may leave two unequal positions tied; a walk cannot, because a
     * walk that met such a pair would take them for one position. So every walk asks for its order
     * here, and a domain that turns out not to tell two of its own positions apart is found at the
     * walk that needed it rather than in whatever the walk went on to answer.
     *
     * @param these what is being walked
     * @param at    the position each of them is at, which is what this order is over
     * @throws IllegalStateException where two of {@code these} are at positions this cannot tell
     *         apart and are not at one position
     */
    default <T> List<T> walking(Collection<T> these, Function<T, A> at) {
        List<T> out = new ArrayList<>(these);
        out.sort(Comparator.comparing(at, this));
        for (int next = 1; next < out.size(); next++) {
            A before = at.apply(out.get(next - 1));
            A here = at.apply(out.get(next));
            if (compare(before, here) == 0 && !before.equals(here)) {
                // The pair named in one order, which is not the order it happened to arrive in. A
                // sort leaves a tie where it found it, so naming them as they lie would tell two
                // callers that wrote one thing two ways two different things about one pair — the
                // very reading this refusal exists to stop.
                throw new IllegalStateException("two positions are one to the order they are walked"
                        + " in and are not one position: " + InOneOrder.of(List.of(before, here)));
            }
        }
        return Collections.unmodifiableList(out);
    }

    /**
     * The order a domain whose positions compare consistently with their own equality already has.
     *
     * <p>For a position that is a string, a number or an enum constant, whose {@code compareTo} is
     * what its own equality is. Such a domain has nothing of its own to say here, and saying it
     * again would be a second spelling of the same order to fall out of step with the first.
     *
     * <p><b>And {@link Comparable} is not asked to promise more than this needs.</b> It does not
     * promise that a comparison of nought is equality — two decimals written to different scales
     * compare as one and are two values — and neither does this. Where such a pair reaches a walk it
     * is refused at {@link #walking}, which is the same place every other domain's coarseness is
     * refused, so nothing here rests on which comparables happen to be consistent.
     */
    static <A extends Comparable<A>> CanonicalOrder<A> asTheyCompare() {
        return Comparable::compareTo;
    }
}
