package souther.compiler.inputs;

import souther.compiler.observe.ObservedValue;

/**
 * The bound an author may declare on the data holding an input, where every run stops in an
 * operation past where the representation of its number stops: the place as that data's
 * invariant names it, the side, and the least bound that keeps every run from stopping there.
 *
 * <p>Where the representation stops is no line the model draws: a birthday in year −999999999 is
 * no birthday a specification means, and the bound that keeps a run from it is the domain's to
 * choose. So what is said is the side and how far it may go at the most, and not where it should
 * be: a birthday from 1900 on is the author's, and this says only that it is from the second day
 * there is.
 *
 * @param data   the data whose invariant names the place
 * @param named  the place as that invariant names it: a field of the data, or its value where the
 *               data is the place's own type
 * @param atMost whether the bound holds the place from above
 * @param bound  the value at the bound, as a row would hold it
 */
public record ABoundThatKeepsEveryRunGoing(String data, String named, boolean atMost,
                                           ObservedValue bound) {

    public ABoundThatKeepsEveryRunGoing {
        if (data == null || named == null || bound == null) {
            throw new IllegalArgumentException("a bound is on a place some data names, at a value");
        }
    }
}
