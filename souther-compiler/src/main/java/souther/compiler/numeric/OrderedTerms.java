package souther.compiler.numeric;

import java.util.Iterator;
import java.util.Map;
import java.util.NoSuchElementException;

/**
 * The terms of a sum in the order they are added in, held as a pair of arrays.
 *
 * <p>For a sum made once, read once and let go: the residual a premise leaves a form is added up
 * and forgotten, and holding it in a map built for the purpose costs a table, a node per term and
 * an iterator, where all that is asked of it is the order. What is held is exactly what a
 * {@link java.util.LinkedHashMap} of the same terms iterates in, a position once and in the order it
 * arrived in.
 *
 * <p>Walked as map entries, so that {@link Reach} sums these as it sums a map's. The one entry
 * handed out is reused for every term, and is only good until the walk moves on.
 */
final class OrderedTerms<A> implements Iterable<Map.Entry<A, ExactRatio>> {

    private final Object[] positions;
    private final ExactRatio[] weights;
    private int size;

    /** Room for {@code capacity} terms, which {@link #addUnlessNought} does not grow past. */
    OrderedTerms(int capacity) {
        this.positions = new Object[capacity];
        this.weights = new ExactRatio[capacity];
    }

    /** {@code position} weighed by {@code weight}, after the terms already here; nothing where the
     *  weight is nought, which no sum has a term for. */
    void addUnlessNought(A position, ExactRatio weight) {
        if (weight.isZero()) {
            return;
        }
        positions[size] = position;
        weights[size] = weight;
        size++;
    }

    int size() {
        return size;
    }

    @SuppressWarnings("unchecked")
    private A position(int at) {
        return (A) positions[at];
    }

    private ExactRatio weight(int at) {
        return weights[at];
    }

    @Override
    public Iterator<Map.Entry<A, ExactRatio>> iterator() {
        return new Walk();
    }

    private final class Walk implements Iterator<Map.Entry<A, ExactRatio>>, Map.Entry<A, ExactRatio> {

        private int next;

        @Override
        public boolean hasNext() {
            return next < size;
        }

        @Override
        public Map.Entry<A, ExactRatio> next() {
            if (next >= size) {
                throw new NoSuchElementException();
            }
            next++;
            return this;
        }

        @Override
        public A getKey() {
            return position(next - 1);
        }

        @Override
        public ExactRatio getValue() {
            return weight(next - 1);
        }

        @Override
        public ExactRatio setValue(ExactRatio value) {
            throw new UnsupportedOperationException("the terms of a sum are not changed in the walk");
        }
    }
}
