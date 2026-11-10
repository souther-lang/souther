package souther.compiler.inputs;

import souther.compiler.diag.SourcePos;
import souther.compiler.numeric.Rel;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * What a run has to meet to get past one construction it works out on the way to a rule: the
 * numbers the construction is made of lie where the clauses of the type made leave them.
 *
 * <p>A condition on the run and not a row that stops: a construction asks it of every run that
 * works it out, and a run that does not meet it ends there. Which rows meet it is the way to the
 * rule's to say, and where the declarations already hold it, nothing is asked of a run here and no
 * construction is said.
 *
 * <p>What a run holds is what it holds where the construction is worked out: a guard the run
 * passed before it leaves out what the guard holds, and a guard the run meets only after it
 * leaves out nothing, since the construction ended the run first.
 *
 * <p>Said of the construction as the model wrote it, so two constructions that ask the same are
 * two of these, as they are two places a run may end.
 *
 * <p>The same condition is what narrows the rows the rule is read over; this is that condition
 * told, and nothing here is worked out again from the text.
 *
 * @param construction the type made, as it is written
 * @param at           where the construction is written
 * @param asks         what it asks
 * @param bearing      which rules what it asks is said under
 */
public record WhatAConstructionAsks(String construction, SourcePos at, Asked asks,
                                    Bearing bearing) {

    public WhatAConstructionAsks {
        if (construction == null || at == null || asks == null || bearing == null) {
            throw new IllegalArgumentException("a construction of some type asks something");
        }
    }

    /** Whether a rule that reads {@code reads} is one this is said under. */
    public boolean bearsOn(Set<TermPath> reads) {
        return bearing.bearsOn(reads);
    }

    /**
     * Which rules what a construction asks is said under: the construction asks the same of every
     * run that works it out, and a rule that reads none of the places its numbers are of is
     * about nothing it asks, so said under every rule it would be said once for each rule.
     */
    public sealed interface Bearing permits OnPlaces, OnEveryRule {

        /** Whether a rule that reads {@code reads} is one this is said under. */
        boolean bearsOn(Set<TermPath> reads);
    }

    /** Of numbers of these places: the rules that read one of them. */
    public record OnPlaces(Set<TermPath> places) implements Bearing {

        public OnPlaces {
            if (places.isEmpty()) {
                throw new IllegalArgumentException("numbers of no place bear on every rule: "
                        + "that is OnEveryRule");
            }
            places = Collections.unmodifiableSet(new LinkedHashSet<>(places));
        }

        @Override
        public boolean bearsOn(Set<TermPath> reads) {
            return reads.stream().anyMatch(read ->
                    places.stream().anyMatch(place -> place.bearsOn(read)));
        }
    }

    /** Of a number of no place that can be named, or of none: every rule, since nothing says
     *  which it is about. */
    public record OnEveryRule() implements Bearing {

        @Override
        public boolean bearsOn(Set<TermPath> reads) {
            return true;
        }
    }

    /** What is asked of the numbers of the input. */
    public sealed interface Asked permits Never, Is, AllOf, OneOf {}

    /**
     * No run gets past the construction: what it asks is met by no run, as the lesser of a number
     * below nought and any other is below nought and so never at nought or above. Said of the
     * construction whole, and never as a part of what else is asked, since a part no run meets
     * settles what it is a part of.
     */
    public record Never() implements Asked {}

    /**
     * One form of the numbers of the input stands {@code rel} to a number.
     *
     * @param form    the numbers weighed and a constant, as an author would write them
     * @param rel     how it stands to {@code against}
     * @param against the number, written as a decimal
     */
    public record Is(String form, Rel rel, String against) implements Asked {

        public Is {
            if (form == null || rel == null || against == null) {
                throw new IllegalArgumentException("a form stands some way to some number");
            }
        }
    }

    /** Every one of these is asked. */
    public record AllOf(List<Asked> each) implements Asked {

        public AllOf {
            each = List.copyOf(each);
            if (each.size() < 2) {
                throw new IllegalArgumentException("two things asked together, or one asked alone");
            }
        }
    }

    /** At least one of these is asked to hold. */
    public record OneOf(List<Asked> each) implements Asked {

        public OneOf {
            each = List.copyOf(each);
            if (each.size() < 2) {
                throw new IllegalArgumentException("two things one of which holds, or one alone");
            }
        }
    }
}
