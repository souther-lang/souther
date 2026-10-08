package souther.compiler.partition;

import souther.compiler.core.Core;
import souther.compiler.meaning.Proposition;

import java.util.List;
import java.util.Optional;

/**
 * Which answers a truth can give — as far as what the source wrote says.
 *
 * <p>Read off what the truth states ({@link Pullback}), so an operation the library says walks a
 * container is read by the element that witnesses it, and a closure fixed at one answer carries that
 * answer through: {@code List.all(_ -> true, xs)} is true whatever {@code xs} is, and
 * {@code List.any(_ -> true, xs)} is whether {@code xs} holds anything. Nothing here reads the
 * condition a second time.
 *
 * <p>Five answers and not two ({@link Outcomes}). A value the same whatever the input gives one
 * answer, and which one is a second question this can answer for some values and not others; and
 * whether it is the same whatever the input is a third, which a value made of one this cannot name
 * and one that varies cannot always answer.
 */
final class TruthOutcomes {

    private TruthOutcomes() {
    }

    /**
     * Which answers something can give, as far as this reading can say.
     *
     * <p>Of a truth, true and false.
     */
    enum Outcomes {
        /** It may come out either way. */
        EITHER,
        /** It comes out true and never false. */
        ONLY_TRUE,
        /** It comes out false and never true. */
        ONLY_FALSE,
        /**
         * It comes out one way whatever the input, and which one this reading cannot say.
         *
         * <p>No way is stood behind, which is what the tree's own reading answers of a value it
         * cannot witness: the way through it is kept as one, and nothing is claimed of either.
         */
        FIXED_UNNAMED,
        /**
         * This reading cannot say even whether it is the same whatever the input.
         *
         * <p>A value made of one fixed at an answer nobody named and one that varies: which of the
         * two decides it is the answer nobody named. No way is stood behind, as above, and it is
         * not taken for fixed.
         */
        UNKNOWN;

        /** Whether some input brings it out {@code want}, as far as this reading stands behind. */
        boolean allows(boolean want) {
            return switch (this) {
                case EITHER -> true;
                case ONLY_TRUE -> want;
                case ONLY_FALSE -> !want;
                case FIXED_UNNAMED, UNKNOWN -> false;
            };
        }

        /** Whether it comes out {@code value} for every input, which this reading can say. */
        boolean always(boolean value) {
            return this == only(value);
        }

        /** Whether it is the same whatever the input. */
        boolean isFixed() {
            return switch (this) {
                case ONLY_TRUE, ONLY_FALSE, FIXED_UNNAMED -> true;
                case EITHER, UNKNOWN -> false;
            };
        }

        Outcomes denied() {
            return switch (this) {
                case ONLY_TRUE -> ONLY_FALSE;
                case ONLY_FALSE -> ONLY_TRUE;
                case EITHER, FIXED_UNNAMED, UNKNOWN -> this;
            };
        }

        static Outcomes only(boolean value) {
            return value ? ONLY_TRUE : ONLY_FALSE;
        }

        /**
         * Both holding.
         *
         * <p>Either part failing settles it, and one that always holds leaves the other. Two that
         * vary vary together and two fixed are fixed; one fixed at an answer nobody named beside
         * one that varies is either, or false, by the answer nobody named.
         */
        Outcomes and(Outcomes other) {
            if (this == ONLY_FALSE || other == ONLY_FALSE) {
                return ONLY_FALSE;
            }
            if (this == ONLY_TRUE) {
                return other;
            }
            if (other == ONLY_TRUE) {
                return this;
            }
            if (this == other && this != UNKNOWN) {
                return this;
            }
            return UNKNOWN;
        }

        /** Either holding. */
        Outcomes or(Outcomes other) {
            return denied().and(other.denied()).denied();
        }

        /**
         * What comes out on whichever of several applications a run meets it on, each giving
         * {@code each}: every answer one of them gives. Where one is fixed at an answer nobody
         * named, another may be fixed at the other, so nothing is stood behind.
         */
        static Outcomes onSomeApplication(List<Outcomes> each) {
            if (each.stream().anyMatch(one -> one == FIXED_UNNAMED || one == UNKNOWN)) {
                return UNKNOWN;
            }
            return each.stream().distinct().count() == 1 ? each.getFirst() : EITHER;
        }
    }

    /**
     * Which answers {@code truth} can give.
     *
     * @param names what the names in it stand for
     */
    static Outcomes ofTheTruth(Core truth, WhatNamesStandFor names) {
        return of(Pullback.ofATruth(truth, names.reads(), names.read(), Optional.empty())
                .proposition());
    }

    /**
     * Which answers what {@code stated} states can give.
     *
     * <p>A part about a subject a row controls can come out either way, and one nothing read can
     * come out only as far as it is known to: the same every time, or either. A part joined to
     * another is what the two can give together. Some element meeting a part is false where none
     * can meet it; where every element can, it is whether the container holds one, and a container
     * at a position may or may not.
     */
    static Outcomes of(Proposition stated) {
        return switch (stated) {
            case Proposition.Always(boolean holds) -> Outcomes.only(holds);
            case Proposition.Compared _, Proposition.Truth _, Proposition.InCases _,
                 Proposition.Present _, Proposition.SameValue _ -> Outcomes.EITHER;
            case Proposition.Unread unread ->
                    unread.fixed() ? Outcomes.FIXED_UNNAMED : Outcomes.EITHER;
            case Proposition.All all -> all.parts().stream().map(TruthOutcomes::of)
                    .reduce(Outcomes.ONLY_TRUE, Outcomes::and);
            case Proposition.Any any -> any.parts().stream().map(TruthOutcomes::of)
                    .reduce(Outcomes.ONLY_FALSE, Outcomes::or);
            case Proposition.OnAnApplication applications -> Outcomes.onSomeApplication(
                    applications.each().stream().map(TruthOutcomes::of).toList());
            case Proposition.Some some -> {
                Outcomes found = switch (of(some.ofTheElement())) {
                    case ONLY_FALSE -> Outcomes.ONLY_FALSE;
                    case ONLY_TRUE, EITHER -> Outcomes.EITHER;
                    case FIXED_UNNAMED, UNKNOWN -> Outcomes.UNKNOWN;
                };
                yield some.holds() ? found : found.denied();
            }
        };
    }
}
