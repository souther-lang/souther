package souther.compiler.inputs;

import souther.compiler.observe.ObservedValue;

/**
 * The bound an author may declare on the data holding an input, where a run may stop in an
 * operation past where the representation of its number stops: what holds the place, the side,
 * and a bound within which no run stops there.
 *
 * <p>Where the representation stops is no line the model draws: a birthday in year −999999999 is
 * no birthday a specification means, and the bound that keeps a run from it is the domain's to
 * choose. So what is said is the side and how far it may go, and not where it should be: a
 * birthday from 1900 on is the author's, and this says only that it is from the second day there
 * is.
 *
 * @param holder      what the invariant is declared on: a data that holds the place, or, for a
 *                    parameter no data holds, a data the author introduces to hold it
 * @param atMost      whether the bound holds the place from above
 * @param bound       the value at the bound, as a row would hold it
 * @param furthestOut whether it is as far out as a bound can be: a run with the place one step
 *                    past it is shown to stop. Otherwise it is enough to keep every run from the
 *                    stop, and nothing is said of how far out one may go
 */
public record ABoundThatKeepsEveryRunGoing(Holder holder, boolean atMost, ObservedValue bound,
                                           boolean furthestOut) {

    public ABoundThatKeepsEveryRunGoing {
        if (holder == null || bound == null) {
            throw new IllegalArgumentException("a bound is on a place something holds, at a value");
        }
    }

    /** What an invariant keeping a run from the stop is declared on. */
    public sealed interface Holder {

        /** The place as the invariant names it. */
        String named();

        /**
         * A data the model declares.
         *
         * @param data  the data whose invariant names the place
         * @param named the place as that invariant names it: a field of the data, or its value
         *              where the data is the place's own type
         */
        record AData(String data, String named) implements Holder {

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
