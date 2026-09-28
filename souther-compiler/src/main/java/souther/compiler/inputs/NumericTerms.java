package souther.compiler.inputs;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

/**
 * The one order the terms of a numeric form are walked in.
 *
 * <p>A form is a mapping from terms to coefficients, and what a mapping is equal to says nothing
 * about the order it was filled in. {@code 6 * b + 3 * a} and {@code 3 * a + 6 * b} are one form,
 * written two ways. So a reader taking the terms off the mapping is reading the order the author
 * happened to write them in, or the order some earlier walk happened to reach them in, while
 * nothing comparing two forms can see any difference between them. Two readers doing that
 * separately can disagree, and one reader can disagree with itself after a rewrite that changed
 * nothing.
 *
 * <p>Here rather than at each reader, because it is one answer. It was already written out twice —
 * once for what a document names, once for which coordinate a reading files at — and everywhere
 * else the mapping was walked as it came.
 *
 * <p><b>Not a natural order on a term.</b> Nothing about what a term is puts it before or after
 * another; what is here is an order to walk a form in, which is a smaller claim. A term is not
 * {@link Comparable} and a mapping keyed by one is not a sorted mapping: an order carried on the
 * term itself would be an order every reader of a term could reach for, and what settles a reading
 * of a form is arithmetic rather than spelling.
 *
 * <p><b>And two terms are never walked as one.</b> What puts these in an order is a name written
 * for each, and a name is not what tells two terms apart. A walk that took two for one would hand
 * over one coefficient twice and the other never, and the form would come out a term short with
 * nothing about the arithmetic looking wrong — so it is refused where it would happen.
 */
public final class NumericTerms {

    private NumericTerms() {}

    /** These terms, in the one order. */
    public static List<NumericTerm> inOrder(Collection<NumericTerm> terms) {
        return walked(new ArrayList<>(terms), NumericTerms::nameOf);
    }

    /** What a form holds, walked by its terms. */
    public static <V> List<Map.Entry<NumericTerm, V>> entriesInOrder(Map<NumericTerm, V> form) {
        return walked(new ArrayList<>(form.entrySet()), each -> nameOf(each.getKey()));
    }

    private static <T> List<T> walked(List<T> these, Function<T, String> naming) {
        these.sort(Comparator.comparing(naming));
        for (int at = 1; at < these.size(); at++) {
            T before = these.get(at - 1);
            T here = these.get(at);
            if (naming.apply(before).equals(naming.apply(here)) && !before.equals(here)) {
                throw new IllegalStateException("two terms of one form are written alike: "
                        + before + " and " + here + "; a form holds one coefficient per term, and"
                        + " a walk by the names would hand one of them over twice and the other"
                        + " never");
            }
        }
        return List.copyOf(these);
    }

    /**
     * The name a term is walked under: what it is written as, and then which kind of term it is.
     *
     * <p>Written first, because that is what a reader of a form meets. A form named in a report is
     * a document held against the one written last time, and the terms of it stand in the order
     * their names put them in.
     *
     * <p>The kind after it, because a name is not what tells two terms apart: a number read at a
     * place and a number taken of what is at that place can be spelled alike and are two terms.
     * Carried second, it separates those two without moving anything their names already told
     * apart.
     */
    private static String nameOf(NumericTerm term) {
        return term + " " + switch (term) {
            case NumericTerm.ValueOf _ -> "1";
            case NumericTerm.TakenOf _ -> "2";
            case NumericTerm.TakenOver _ -> "3";
        };
    }
}
