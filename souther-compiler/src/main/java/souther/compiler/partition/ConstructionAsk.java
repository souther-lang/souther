package souther.compiler.partition;

import souther.compiler.diag.SourcePos;
import souther.compiler.inputs.WhatAConstructionAsks;
import souther.compiler.meaning.Proposition;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.function.Predicate;

/**
 * What one construction asks of a run that works it out, as the analysis holds it: a condition on
 * the numbers of the input that a run has to meet to get past it, kept with how each part of it is
 * read so that it can be asked of the way to a rule, and told as the report says it only once that
 * is settled.
 *
 * <p>Not what the report says. Whether the declarations hold it is settled where it is stated, and
 * whether the way to the rule holds it is settled where the way is known; what is said of it is
 * what is left, and what the report says is {@link #toldOf}'s alone.
 *
 * @param construction the type made, as it is written
 * @param at           where the construction is written
 * @param bearing      which rules what it asks is said under
 * @param requirement  what it asks, with what the declarations hold already left out
 */
record ConstructionAsk(String construction, SourcePos at, WhatAConstructionAsks.Bearing bearing,
                       Requirement requirement) {

    ConstructionAsk {
        if (construction == null || at == null || bearing == null || requirement == null) {
            throw new IllegalArgumentException("a construction asks something of some rules");
        }
    }

    /**
     * What the report says this asks of a run whose way holds what {@code heldOnEveryWay} says,
     * or empty where it asks nothing of one: every part the way holds is left out, and a condition
     * nothing is left of is nothing asked.
     *
     * <p>A condition no run meets stays, as the construction no run gets past, and is not nothing.
     */
    Optional<WhatAConstructionAsks> toldOf(Predicate<Proposition> heldOnEveryWay) {
        WhatAConstructionAsks.Asked told = requirement.leavingOut(heldOnEveryWay).told();
        return told == null ? Optional.empty()
                : Optional.of(new WhatAConstructionAsks(construction, at, told, bearing));
    }

    /**
     * A condition on the numbers of the input, of one of five kinds that say everything a
     * condition comes to: nothing, no run, one form standing some way to a number, every one of
     * several, and one of several.
     *
     * <p>Total, and one way to say each: the kinds that are only a constant never stand inside
     * the others, since a constant settles what it stands in ({@link #and}, {@link #or}). So a
     * reader asks which kind it is and never what a missing answer means.
     */
    sealed interface Requirement {

        /** Every run meets it. */
        Requirement ALWAYS = new Always();

        /** No run does. */
        Requirement NEVER = new Never();

        /** Nothing is asked: the declarations, or the way, hold it. */
        record Always() implements Requirement {}

        /** No run gets past: a condition that stands as no number does. */
        record Never() implements Requirement {}

        /**
         * A form of the numbers of the input stands {@code rel} to a number.
         *
         * @param told the form and the number as the report writes them
         * @param read how it was read, which is what the way is asked whether it holds
         */
        record Is(WhatAConstructionAsks.Is told, Proposition read) implements Requirement {}

        /** Every one of these, none of them a constant and at least two. */
        record AllOf(List<Requirement> parts) implements Requirement {

            public AllOf {
                parts = partsOfAChoice(parts, "every one of");
            }
        }

        /** At least one of these, none of them a constant and at least two. */
        record OneOf(List<Requirement> parts) implements Requirement {

            public OneOf {
                parts = partsOfAChoice(parts, "one of");
            }
        }

        private static List<Requirement> partsOfAChoice(List<Requirement> parts, String of) {
            List<Requirement> kept = List.copyOf(parts);
            if (kept.size() < 2 || kept.stream().anyMatch(each -> each instanceof Always
                    || each instanceof Never)) {
                throw new IllegalArgumentException(of + " several conditions is two or more, none "
                        + "of them settled: " + kept);
            }
            return kept;
        }

        /** Both, which is no run where either is none and what the other asks where one asks
         *  nothing. */
        static Requirement and(Requirement first, Requirement second) {
            if (first instanceof Never || second instanceof Never) {
                return NEVER;
            }
            if (first instanceof Always) {
                return second;
            }
            if (second instanceof Always) {
                return first;
            }
            List<Requirement> parts = new ArrayList<>();
            parts.addAll(first instanceof AllOf all ? all.parts() : List.of(first));
            parts.addAll(second instanceof AllOf all ? all.parts() : List.of(second));
            return new AllOf(parts);
        }

        /** Either, which is nothing asked where either asks nothing and what the other asks where
         *  one is met by no run. */
        static Requirement or(Requirement first, Requirement second) {
            if (first instanceof Always || second instanceof Always) {
                return ALWAYS;
            }
            if (first instanceof Never) {
                return second;
            }
            if (second instanceof Never) {
                return first;
            }
            List<Requirement> parts = new ArrayList<>();
            parts.addAll(first instanceof OneOf one ? one.parts() : List.of(first));
            parts.addAll(second instanceof OneOf one ? one.parts() : List.of(second));
            return new OneOf(parts);
        }

        /** This with every part that {@code held} says holds on every way left out. */
        default Requirement leavingOut(Predicate<Proposition> held) {
            return switch (this) {
                case Always _, Never _ -> this;
                case Is is -> held.test(is.read()) ? ALWAYS : this;
                case AllOf all -> all.parts().stream().map(part -> part.leavingOut(held))
                        .reduce(ALWAYS, Requirement::and);
                case OneOf one -> one.parts().stream().map(part -> part.leavingOut(held))
                        .reduce(NEVER, Requirement::or);
            };
        }

        /** What the report says of it, or null where nothing is asked. */
        default WhatAConstructionAsks.Asked told() {
            return switch (this) {
                case Always _ -> null;
                case Never _ -> new WhatAConstructionAsks.Never();
                case Is is -> is.told();
                case AllOf all -> new WhatAConstructionAsks.AllOf(
                        all.parts().stream().map(Requirement::told).toList());
                case OneOf one -> new WhatAConstructionAsks.OneOf(
                        one.parts().stream().map(Requirement::told).toList());
            };
        }
    }
}
