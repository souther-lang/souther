package souther.compiler.meaning;

import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ExpansionSite;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Objects;
import java.util.Optional;

/**
 * A choice the author of a comparison wrote, as the comparison's own definition has it: which
 * construct, and through which calls that definition makes.
 *
 * <p>A comparison in a helper is read once per call, and each copy reaches values two ways. What the
 * definition computes from its parameters — an {@code if} in an operand, the cases of an operation
 * it applies, the body of a helper it calls — is the same in every copy, and a choice there divides
 * what the author wrote into lines. What a parameter is given is the caller's, different in each
 * copy, and a choice there divides one line into the places a call put it. Only the first is one of
 * these.
 *
 * <p>Told apart by the copy each construct stands in. The comparison's copy, or a copy made by a
 * call written inside it, is the definition's; any other is something a caller handed in. A copy
 * made by applying a function the definition was given is the caller's too, whatever body it is of:
 * the function is a value of the call.
 *
 * @param origin the construct as the source wrote it
 * @param within the calls between the comparison's definition and the construct, outermost first;
 *               empty where the definition wrote the construct itself
 */
public record WrittenChoice(SourceConstructOrigin origin, List<ExpansionLineage.Step> within) {

    public WrittenChoice {
        Objects.requireNonNull(origin, "a choice is some construct");
        within = List.copyOf(within);
    }

    /**
     * The choices in the order a reader that has nothing else to go on puts them in: by the
     * construct, then by the calls it is reached through, outermost first.
     *
     * <p>Told by what the document publishes a choice by (the construct and the sites between),
     * so two choices it tells apart are two here. A call the caller handed in is no part of a
     * choice ({@link #of}), so a supplied site here is a mistake and not an order.
     *
     * <p>By the site and not by what was expanded there, because a site the source wrote expands
     * one thing: a call is of one function, a name stands for one block. Two steps at one site that
     * expand different things would break that, and are refused rather than put together.
     */
    public static Comparator<WrittenChoice> inASteadyOrder() {
        return Comparator.comparing(WrittenChoice::origin, SourceConstructOrigin.inASteadyOrder())
                .thenComparing(WrittenChoice::within, WrittenChoice::inTheOrderCalled);
    }

    private static int inTheOrderCalled(List<ExpansionLineage.Step> one,
                                        List<ExpansionLineage.Step> other) {
        for (int at = 0; at < Math.min(one.size(), other.size()); at++) {
            int order = ExpansionSite.inASteadyOrder()
                    .compare(direct(one.get(at).at()), direct(other.get(at).at()));
            if (order != 0) {
                return order;
            }
            if (!one.get(at).expanded().equals(other.get(at).expanded())) {
                throw new IllegalStateException("one site the source wrote expands one thing, and"
                        + " this expands " + one.get(at).expanded() + " and "
                        + other.get(at).expanded() + ": " + one.get(at).at());
            }
        }
        return Integer.compare(one.size(), other.size());
    }

    private static ExpansionSite.Direct direct(ExpansionSite site) {
        if (site instanceof ExpansionSite.Direct direct) {
            return direct;
        }
        throw new IllegalStateException("a choice is reached through calls its definition writes,"
                + " and a supplied site is the caller's: " + site);
    }

    /**
     * The choice {@code construct} is, where the definition of a comparison standing in
     * {@code comparison} wrote it — or nothing, where a caller handed it in.
     */
    public static Optional<WrittenChoice> of(ConstructOccurrence construct,
                                             ExpansionLineage comparison) {
        if (!construct.isWritten()) {
            return Optional.empty();
        }
        List<ExpansionLineage.Step> between = new ArrayList<>();
        ExpansionLineage at = construct.lineage().expansionProjection();
        while (!at.equals(comparison)) {
            if (!(at instanceof ExpansionLineage.Expansion copy)
                    || copy.expanded() instanceof ValueName.Local
                    || copy.at() instanceof ExpansionSite.Supplied) {
                return Optional.empty();
            }
            between.add(copy.step());
            at = copy.within();
        }
        Collections.reverse(between);
        return Optional.of(new WrittenChoice(construct.origin(), between));
    }
}
