package souther.compiler.inputs;

import souther.compiler.check.RuleKey;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.TypeSymbol;

import java.math.BigInteger;

/**
 * One bound an author may declare on the data holding an input, as one of the bounds that together
 * keep every run from a stop past where the representation of a number stops
 * ({@link WhatKeepsEveryRunGoing}): what holds the place, the side, and the value. Which bound it
 * is, and nothing of what is shown of it.
 *
 * <p>Where the representation stops is no line the model draws: a birthday in year −999999999 is
 * no birthday a specification means, and the bound that keeps a run from it is the domain's to
 * choose. So what is said is the side and how far it may go, and not where it should be: a
 * birthday from 1900 on is the author's, and this says only that it is from the second day there
 * is.
 *
 * <p>Which bound it is is what it is declared on and the side: an invariant holds every value of
 * the data, so two places the one data holds are bounded by the one declaration, and a bound on
 * one of them is a bound on both.
 *
 * @param holder what the invariant is declared on: a data that holds the place, or, for a
 *               parameter no data holds, a data the author introduces to hold it
 * @param atMost whether the bound holds the value from above
 * @param at     the whole number the value holds at the bound: the number, or the count of the
 *               days of a date
 * @param bound  the value at the bound, as a row would hold it
 */
public record ABoundThatKeepsEveryRunGoing(Holder holder, boolean atMost, BigInteger at,
                                           ObservedValue bound) {

    public ABoundThatKeepsEveryRunGoing {
        if (holder == null || at == null || bound == null) {
            throw new IllegalArgumentException("a bound is on what something holds, at a value");
        }
    }

    /**
     * The least and greatest whole number the rules already written and the value's own type leave
     * what a bound is declared on, every one between them a value: each null where neither has an
     * end there. A bound past one of them leaves no value, and a bound outside both asks nothing.
     *
     * <p>An account of the holder, which a reading gives as it reads the input, and no part of a
     * bound: two readings may give two accounts of one holder, and a bound is declared beside
     * every one of them ({@link WhatKeepsEveryRunGoing}).
     */
    public record Held(BigInteger least, BigInteger greatest) {

        /** Whether this leaves no whole number. */
        boolean none() {
            return least != null && greatest != null && least.compareTo(greatest) > 0;
        }

        /** This, with the bound {@code at} on it, from above where {@code atMost}. */
        Held bounded(BigInteger at, boolean atMost) {
            return meet(atMost ? new Held(null, at) : new Held(at, null));
        }

        /** What this and {@code other}, two accounts of what one holder holds, leave it both. */
        Held meet(Held other) {
            return new Held(least == null ? other.least : other.least == null ? least
                    : least.max(other.least),
                    greatest == null ? other.greatest : other.greatest == null ? greatest
                    : greatest.min(other.greatest));
        }

        /** Whether every value this holds is within {@code bound}, from above where
         *  {@code atMost}: a bound there asks nothing of it. */
        public boolean within(BigInteger bound, boolean atMost) {
            return atMost ? greatest != null && greatest.compareTo(bound) <= 0
                    : least != null && least.compareTo(bound) >= 0;
        }

        /** Whether no value this holds is within {@code bound}, from above where {@code atMost}:
         *  declared, it leaves none. */
        public boolean past(BigInteger bound, boolean atMost) {
            return atMost ? least != null && bound.compareTo(least) < 0
                    : greatest != null && bound.compareTo(greatest) > 0;
        }
    }

    /** Which declaration this is: what it is declared on, and the side. */
    record Side(Holder holder, boolean atMost) {}

    Side side() {
        return new Side(holder, atMost);
    }

    /** Whether this keeps the value within {@code other}, a bound of the same side: no further
     *  out. */
    boolean within(ABoundThatKeepsEveryRunGoing other) {
        return atMost ? at.compareTo(other.at) <= 0 : at.compareTo(other.at) >= 0;
    }

    /** What an invariant keeping a run from the stop is declared on. */
    public sealed interface Holder {

        /** What the invariant calls the place, as the rules of what it is declared on name it
         *  ({@link RuleAddress}): the value itself, or a field read from it. */
        RuleKey named();

        /**
         * A data the model declares, which is the declaration and not its name: two modules may
         * each declare a data of one name, and an invariant on one is none on the other.
         *
         * @param data  the data whose invariant names the place
         * @param named what that invariant calls the place: a field of the data, or the value
         *              itself where the data is the place's own type
         */
        record AData(TypeSymbol.AtModule data, RuleKey named) implements Holder {

            public AData {
                if (data == null || named == null) {
                    throw new IllegalArgumentException("a data, and the place as it names it");
                }
            }
        }

        /**
         * A parameter of a behavior whose type is one no data of the model's is: there is no
         * invariant to add a clause to until the author introduces a data of that type and takes
         * the parameter as it, the clause naming the data's value.
         *
         * @param parameter the parameter
         * @param type      its type, as it is written
         */
        record AParameter(String parameter, String type) implements Holder {

            public AParameter {
                if (parameter == null || type == null) {
                    throw new IllegalArgumentException("a parameter, and its type");
                }
            }

            @Override
            public RuleKey named() {
                return RuleKey.THE_VALUE;
            }
        }
    }
}
