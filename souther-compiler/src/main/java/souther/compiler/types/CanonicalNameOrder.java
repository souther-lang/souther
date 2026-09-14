package souther.compiler.types;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Set;

/**
 * The order this compiler shows a set of names in.
 *
 * <p>A union is a set: {@code Adult | Minor} and {@code Minor | Adult} are one value, and the value
 * does not hold which of the two was written. So the order a reader is shown cannot be the author's
 * — there is no author's order on a value two authors reach — and it is this compiler's decision
 * instead. This is where that decision is written down.
 *
 * <p>{@link TypeSymbol}'s own order is the one taken: the name first, because that is what a reader
 * looking down a list reads, and then what tells two of one spelling apart. Named here rather than
 * reached for wherever a set of names becomes a sentence, so that the order is one thing to change
 * and changing it reads as what it is — a change to what readers are shown, not a tidy-up.
 *
 * <p><b>There is no author's order here to keep.</b> The members are read in the order they were
 * written and put in a set, and past that nothing holds which writing it was — a sequence of them
 * further on is one taken back off the set. So a reader that means to quote what somebody wrote
 * cannot be served out of a type at all, and has to be handed the order before the members reach
 * one. That is what the published surface does: it is a declaration rather than a value, the
 * declaration is still in hand, and {@code PublishedCaseOrder} reads the order off it. Taken from
 * here instead, the standard library's {@code Int | DivisionByZero} would be published as
 * {@code DivisionByZero | Int} — the reason there is no value, before the value.
 *
 * <p><b>Every reader of one union answers about the same union.</b> Two of them ordering it
 * differently is two answers to a question the type does not have, so the atoms a union is
 * descended into, what a report says a subject is made of, and what a message names it as all come
 * from here. What one of them orders differently, it orders because of how a set happened to be
 * built.
 *
 * <p><b>What is not here is an order that decides something.</b> A walk choosing which case to act
 * on is not showing anything, and what it needs is a rule for which case that is. An order made for
 * readers can be used as one — the names compare, so a walk can take the first — and a walk that
 * does is one whose answer moves when what readers are shown is changed.
 *
 * <p><b>One owner, and two ways of being one.</b> An order a plurality does not have of its own has
 * to be established somewhere that goes on governing every reading of it, or a reader downstream
 * is left working out again what somebody upstream already decided.
 *
 * <p>Sometimes that place is the crossing. A set arranged here immediately before the one reader
 * that shows it is in this order for as long as the expression lasts and is held by nobody, so the
 * claim is the call — which is what a plurality reaching a report cannot do, because between being
 * handed one and reading it lies everything a consumer might do with the order, and there the
 * order is said by the type it crosses as. {@code PublishedCaseOrder} and the case names of a
 * report take a plain set from wherever their callers had one, so each of those owns the order of
 * what it was handed.
 *
 * <p>Sometimes the value owns it instead. {@link Type.Union} puts its members in this order where
 * it is built, so every later reading of them is in it by having done nothing — no walk over a
 * union has an order to decide, and a reader written afterwards is right without knowing this
 * class exists. Where that holds, arranging the members again is a second owner of one order, and
 * the one that goes untested is whichever of the two somebody later changes.
 */
public final class CanonicalNameOrder {

    private CanonicalNameOrder() {
    }

    /**
     * {@code names}, in the order they are shown.
     *
     * <p>Sorted in a list of its own rather than through a stream. Every union arranges its members
     * here as it is built, so what this is asked of is a handful of names and it is asked often;
     * a pipeline and the buffer it sorts into cost more than the sort does at that size.
     */
    public static List<TypeSymbol> shown(Set<TypeSymbol> names) {
        List<TypeSymbol> shown = new ArrayList<>(names);
        shown.sort(Comparator.naturalOrder());
        return Collections.unmodifiableList(shown);
    }
}
