package souther.compiler.inputs;

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
 * @param held   the whole numbers the rules already written leave what is declared on, every one
 *               of which is a value: what the bound is declared beside
 */
public record ABoundThatKeepsEveryRunGoing(Holder holder, boolean atMost, BigInteger at,
                                           ObservedValue bound, Held held) {

    public ABoundThatKeepsEveryRunGoing {
        if (holder == null || at == null || bound == null || held == null) {
            throw new IllegalArgumentException("a bound is on what something holds, at a value");
        }
    }

    /**
     * The least and greatest whole number the rules already written leave a value, every one
     * between them a value: each null where they leave no end there beside what the value's type
     * holds.
     */
    public record Held(BigInteger least, BigInteger greatest) {}

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

        /** The place as the invariant names it. */
        String named();

        /**
         * A data the model declares, which is the declaration and not its name: two modules may
         * each declare a data of one name, and an invariant on one is none on the other.
         *
         * @param data  the data whose invariant names the place
         * @param named the place as that invariant names it: a field of the data, or its value
         *              where the data is the place's own type
         */
        record AData(TypeSymbol.AtModule data, String named) implements Holder {

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
            public String named() {
                return "value";
            }
        }
    }
}
