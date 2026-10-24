package souther.compiler.partition;

import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.Shape;
import souther.compiler.check.TypeView;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.function.Function;

/**
 * The values one step from a value a run was seen taking, for a search that looks beside where it
 * knows a run comes back.
 *
 * <p>One whole number is moved by one and everything else stays as it was, wherever the number sits:
 * inside a newtype, a field of a record, an element of a list. Which leaves are whole numbers is the
 * position's type to say and not the value's: a boundary carries a whole number where a
 * {@code Decimal} stands, and a decimal has no value directly beside it, so none is invented for it.
 * The walk into a value is the one a value is written back with ({@code ObservedFixtures}), so a
 * newtype, a field and an element are read as a fixture reads them.
 *
 * <p>Handed over one at a time. The search asks for as many as its runs allow, so the work of making
 * a candidate follows the candidates asked for and not the number of leaves a value has.
 */
final class NearbyValues {

    /** What one step from a scalar leaf is. */
    @FunctionalInterface
    private interface Leaves {

        Iterator<ObservedValue> beside(Type.Prim prim, ObservedValue leaf);
    }

    private static final Leaves WHOLE_NUMBERS = (prim, leaf) ->
            prim == Type.Prim.INT && leaf instanceof ObservedValue.Integer whole
                    ? stepsOf(whole) : none();

    /** The values one step from {@code value}, standing at a position of {@code type}. */
    static Iterator<ObservedValue> of(ObservedValue value, Type type, RuleReadingContext reading) {
        return of(value, type, reading, WHOLE_NUMBERS);
    }

    /**
     * The values {@code value} becomes where one string it holds is put as the pieces a body
     * splits it into meeting what the body goes on to demand of each ({@link StringDemands}), and
     * everything else stays as it was — wherever the string sits, as for {@link #of}.
     */
    static Iterator<ObservedValue> demanded(ObservedValue value, Type type,
                                            RuleReadingContext reading, StringDemands demands,
                                            Function<Type, List<String>> standingFor) {
        return of(value, type, reading, (prim, leaf) ->
                prim == Type.Prim.STRING && leaf instanceof ObservedValue.Text text
                        ? mapped(demands.besides(text.value(), standingFor).iterator(),
                                ObservedValue.Text::new)
                        : none());
    }

    private static Iterator<ObservedValue> of(ObservedValue value, Type type,
                                              RuleReadingContext reading, Leaves leaves) {
        if (value.unread() != null) {
            return none();
        }
        var source = reading.source();
        TypeView view = TypeView.of(type, source.inners(), source.symbols(), source.kinds(),
                source.sums());
        ObservedValue inside = ObservedValue.wearing(view.wrappers(), value);
        if (inside == null || inside.unread() != null) {
            return none();
        }
        return mapped(within(inside, view.shape(), reading, leaves),
                near -> ObservedValue.wrapped(view.wrappers(), near));
    }

    private static Iterator<ObservedValue> within(ObservedValue value, Shape shape,
                                                  RuleReadingContext reading, Leaves leaves) {
        return switch (shape) {
            case Shape.Scalar scalar -> leaves.beside(scalar.prim(), value);
            case Shape.Product product -> value instanceof ObservedValue.Constructed made
                    && made.type().equals(product.name())
                    ? fieldsOf(made, product, reading, leaves) : none();
            case Shape.Sequence sequence -> value instanceof ObservedValue.Sequence held
                    ? elementsOf(held, sequence, reading, leaves) : none();
            // The case the value is, as a fixture writes a sum.
            case Shape.Sum sum -> value instanceof ObservedValue.Constructed made
                    && sum.reaches().cases().contains(made.type())
                    ? of(value, Type.ref(made.type()), reading, leaves) : none();
            case Shape.Optional optional -> value instanceof ObservedValue.Absent ? none()
                    : of(value, optional.element(), reading, leaves);
            // Nothing is beside these: a map's keys and a unit case are not a number, and a
            // position nothing writes a value at has no neighbour to write.
            case Shape.Mapping _, Shape.Unit _, Shape.Unresolved _, Shape.Cases _, Shape.Tuple _,
                 Shape.Function _, Shape.Uninhabited _, Shape.Bottom _, Shape.Erroneous _,
                 Shape.Undecided _ -> none();
        };
    }

    private static Iterator<ObservedValue> stepsOf(ObservedValue.Integer whole) {
        List<ObservedValue> out = new ArrayList<>(2);
        if (whole.value() != Long.MAX_VALUE) {
            out.add(new ObservedValue.Integer(whole.value() + 1));
        }
        if (whole.value() != Long.MIN_VALUE) {
            out.add(new ObservedValue.Integer(whole.value() - 1));
        }
        return out.iterator();
    }

    /** Field by field in the order the declaration writes them. */
    private static Iterator<ObservedValue> fieldsOf(ObservedValue.Constructed made,
                                                    Shape.Product product,
                                                    RuleReadingContext reading, Leaves leaves) {
        return flat(List.copyOf(product.fields().entrySet()).iterator(), field -> {
            ObservedValue held = made.field(field.getKey());
            if (held == null) {
                return none();
            }
            return mapped(of(held, field.getValue(), reading, leaves), near -> {
                Map<String, ObservedValue> fields = new LinkedHashMap<>(made.fields());
                fields.put(field.getKey(), near);
                return new ObservedValue.Constructed(made.type(), fields);
            });
        });
    }

    private static Iterator<ObservedValue> elementsOf(ObservedValue.Sequence held,
                                                      Shape.Sequence sequence,
                                                      RuleReadingContext reading, Leaves leaves) {
        return flat(indexes(held.elements().size()), at ->
                mapped(of(held.elements().get(at), sequence.element(), reading, leaves), near -> {
                    List<ObservedValue> elements = new ArrayList<>(held.elements());
                    elements.set(at, near);
                    return new ObservedValue.Sequence(elements);
                }));
    }

    private static Iterator<Integer> indexes(int count) {
        return new Iterator<>() {
            private int next;

            @Override
            public boolean hasNext() {
                return next < count;
            }

            @Override
            public Integer next() {
                return next++;
            }
        };
    }

    private static <T> Iterator<T> none() {
        return Collections.emptyIterator();
    }

    /** What {@code how} makes of each, made when it is asked for. */
    private static <A, B> Iterator<B> mapped(Iterator<A> from, Function<A, B> how) {
        return new Iterator<>() {
            @Override
            public boolean hasNext() {
                return from.hasNext();
            }

            @Override
            public B next() {
                return how.apply(from.next());
            }
        };
    }

    /**
     * Everything {@code how} gives for each of {@code outer}, one {@code outer} at a time. A stream's
     * flat map reads the whole of one inner source before handing its first element on, which for
     * a record holding a long list is the list's candidates all made at once.
     */
    private static <A, B> Iterator<B> flat(Iterator<A> outer, Function<A, Iterator<B>> how) {
        return new Iterator<>() {
            private Iterator<B> inner = none();

            @Override
            public boolean hasNext() {
                while (!inner.hasNext() && outer.hasNext()) {
                    inner = how.apply(outer.next());
                }
                return inner.hasNext();
            }

            @Override
            public B next() {
                if (!hasNext()) {
                    throw new NoSuchElementException();
                }
                return inner.next();
            }
        };
    }

    private NearbyValues() {}
}
