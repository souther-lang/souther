package souther.compiler.partition;

import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.Shape;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.PieceDemand;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Optional;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Predicate;

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

    /**
     * A value that stood at a sum on the way to a leaf, and how far into the position that was: the
     * case the value is, which a path to the leaf as a body reads it names as a narrowing.
     */
    private record Narrowing(int depth, ObservedValue value) {}

    /** What a step from a scalar leaf is, given where the leaf stands, the sums on the way to it
     *  and the position it is at. */
    @FunctionalInterface
    private interface Leaves {

        Iterator<ObservedValue> beside(Type.Prim prim, ObservedValue leaf, TermPath at,
                                       List<Narrowing> along, TypeView view);
    }

    private static final Leaves WHOLE_NUMBERS = (prim, leaf, _, _, _) ->
            prim == Type.Prim.INT && leaf instanceof ObservedValue.Integer whole
                    ? stepsOf(whole) : none();

    /** The values one step from {@code value}, standing at a position of {@code type}. */
    static Iterator<ObservedValue> of(ObservedValue value, Type type, RuleReadingContext reading) {
        return of(value, type, reading, null, List.of(), WHOLE_NUMBERS);
    }

    /**
     * The values {@code value}, the one a run had at {@code parameter}, becomes where a string it
     * holds is put as a string a body parts into pieces that are all ones it builds a newtype of
     * ({@link PieceDemand}), and everything else stays as it was.
     *
     * <p>Only the strings that stand where a body parts a string: a demand is about one place of
     * the input, and a string anywhere else is not what the body parts. Handed over one at a time,
     * as the neighbours of a number are, and for as many pieces as the string was seen with and one
     * more, which are the counts a rewrite of which pieces are kept can be told apart at.
     */
    static Iterator<ObservedValue> demanded(ObservedValue value, Type type,
                                            RuleReadingContext reading, String parameter,
                                            List<PieceDemand> demands, List<ObservedValue> row,
                                            Consumer<CompositionBudget> stoppedAt) {
        return of(value, type, reading, TermPath.of(parameter), List.of(),
                (prim, leaf, at, along, view) -> {
            if (prim != Type.Prim.STRING || !(leaf instanceof ObservedValue.Text text)) {
                return none();
            }
            List<PieceDemand> here = demands.stream()
                    .filter(each -> standsAt(each.position(), at, along)).toList();
            Set<String> offered = new HashSet<>(List.of(text.value()));
            Iterator<String> strings = flat(here.iterator(), demand -> flat(
                    shapesOf(text.value(), demand, reading, row, stoppedAt).iterator(),
                    shape -> Partitions.stringsPartedInto(view, reading, demand.attempted(),
                            demand.separator(), demand.through(), shape).iterator()));
            return mapped(filtered(strings, offered::add), ObservedValue.Text::new);
        });
    }

    /**
     * The ways a string is put together of pieces, parted at the separator of {@code demand}, so
     * that some of them are ones the body builds its newtype of and the rest are as they were seen.
     *
     * <p>The nearest first: one piece made a string the newtype admits and no other changed, which
     * is the string a body that goes on to look the piece up in data it was given answers
     * differently on only where the rest is as it was. Then one piece made a string the row holds
     * somewhere else and the newtype admits, which is where a body that looks the piece up in
     * another input of the row can find it. Then every piece made one the newtype admits, for as
     * many pieces as were seen and one more, up to the bound. A string seen in more pieces than the
     * bound is changed at none of them, since the strings made of it are as long as it is and are
     * as many.
     */
    private static List<List<Optional<String>>> shapesOf(String seen, PieceDemand demand,
                                                         RuleReadingContext reading,
                                                         List<ObservedValue> row,
                                                         Consumer<CompositionBudget> stoppedAt) {
        CompositionBudget budget = CompositionBudget.PIECES_A_STRING_IS_PUT_TOGETHER_OF;
        List<String> pieces = partsOf(seen, demand.separator());
        List<List<Optional<String>>> out = new ArrayList<>();
        if (pieces.size() <= budget.maximum()) {
            for (int changed = 0; changed < pieces.size(); changed++) {
                out.add(changing(pieces, changed, Optional.empty()));
            }
            Set<String> held = new LinkedHashSet<>();
            row.forEach(each -> textsIn(each, held));
            held.removeIf(text -> text.codePoints().anyMatch(each -> each == demand.separator())
                    || !Partitions.pieceAdmits(demand.attempted(), reading, demand.through(),
                            text));
            CompositionBudget taken = CompositionBudget.STRINGS_OF_THE_ROW_A_PIECE_IS_TAKEN_FROM;
            if (held.size() > taken.maximum()) {
                stoppedAt.accept(taken);
            }
            for (String text : held.stream().limit(taken.maximum()).toList()) {
                for (int changed = 0; changed < pieces.size(); changed++) {
                    if (!pieces.get(changed).equals(text)) {
                        out.add(changing(pieces, changed, Optional.of(text)));
                    }
                }
            }
        } else {
            stoppedAt.accept(budget);
        }
        if (pieces.size() + 1 > budget.maximum()) {
            stoppedAt.accept(budget);
        }
        for (int count = 1; count <= Math.min(pieces.size() + 1, budget.maximum()); count++) {
            out.add(Collections.nCopies(count, Optional.<String>empty()));
        }
        return out;
    }

    /** {@code pieces} as they were, but for the one at {@code changed}, which is {@code to}. */
    private static List<Optional<String>> changing(List<String> pieces, int changed,
                                                   Optional<String> to) {
        List<Optional<String>> shape = new ArrayList<>();
        for (int at = 0; at < pieces.size(); at++) {
            shape.add(at == changed ? to : Optional.of(pieces.get(at)));
        }
        return shape;
    }

    /** Every string {@code value} holds, wherever in it. */
    private static void textsIn(ObservedValue value, Set<String> out) {
        switch (value) {
            case ObservedValue.Text text -> out.add(text.value());
            case ObservedValue.Constructed made -> made.fields().values()
                    .forEach(each -> textsIn(each, out));
            case ObservedValue.Sequence held -> held.elements()
                    .forEach(each -> textsIn(each, out));
            case ObservedValue.Mapping held -> held.entries().forEach(entry -> {
                textsIn(entry.key(), out);
                textsIn(entry.value(), out);
            });
            default -> { }
        }
    }

    private static List<String> partsOf(String text, int separator) {
        List<String> pieces = new ArrayList<>();
        StringBuilder piece = new StringBuilder();
        text.codePoints().forEach(each -> {
            if (each == separator) {
                pieces.add(piece.toString());
                piece.setLength(0);
            } else {
                piece.appendCodePoint(each);
            }
        });
        pieces.add(piece.toString());
        return pieces;
    }

    /**
     * Whether the leaf at {@code at} is the place {@code position} names, reached through the sums
     * {@code along}.
     *
     * <p>The place is the same without the narrowings, and each narrowing is one the value the walk
     * went through there meets: a place under the case of a sum is a place of the value only when
     * the value is that case, and another case with a field of the same name is another place.
     */
    private static boolean standsAt(TermPath position, TermPath at, List<Narrowing> along) {
        List<TermPath.Step> plain = new ArrayList<>();
        for (TermPath.Step step : position.steps()) {
            if (step instanceof TermPath.Step.Refine refine) {
                int depth = plain.size();
                if (along.stream().noneMatch(each -> each.depth() == depth
                        && refine.cases().leaves(each.value()))) {
                    return false;
                }
            } else {
                plain.add(step);
            }
        }
        return new TermPath(position.head(), plain).equals(at);
    }

    private static Iterator<ObservedValue> of(ObservedValue value, Type type,
                                              RuleReadingContext reading, TermPath at,
                                              List<Narrowing> along, Leaves leaves) {
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
        return mapped(within(inside, view, reading, at, along, leaves),
                near -> ObservedValue.wrapped(view.wrappers(), near));
    }

    private static Iterator<ObservedValue> within(ObservedValue value, TypeView view,
                                                  RuleReadingContext reading, TermPath at,
                                                  List<Narrowing> along, Leaves leaves) {
        return switch (view.shape()) {
            case Shape.Scalar scalar -> leaves.beside(scalar.prim(), value, at, along, view);
            case Shape.Product product -> value instanceof ObservedValue.Constructed made
                    && made.type().equals(product.name())
                    ? fieldsOf(made, product, reading, at, along, leaves) : none();
            case Shape.Sequence sequence -> value instanceof ObservedValue.Sequence held
                    ? elementsOf(held, sequence, reading, at, along, leaves) : none();
            // The case the value is, as a fixture writes a sum.
            case Shape.Sum sum -> value instanceof ObservedValue.Constructed made
                    && sum.reaches().cases().contains(made.type())
                    ? of(value, Type.ref(made.type()), reading, at, narrowed(along, at, value),
                            leaves) : none();
            case Shape.Optional optional -> value instanceof ObservedValue.Absent ? none()
                    : of(value, optional.element(), reading, at, along, leaves);
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
                                                    RuleReadingContext reading, TermPath at,
                                                    List<Narrowing> along, Leaves leaves) {
        return flat(List.copyOf(product.fields().entrySet()).iterator(), field -> {
            ObservedValue held = made.field(field.getKey());
            if (held == null) {
                return none();
            }
            return mapped(of(held, field.getValue(), reading,
                    at == null ? null : at.then(field.getKey()), along, leaves), near -> {
                Map<String, ObservedValue> fields = new LinkedHashMap<>(made.fields());
                fields.put(field.getKey(), near);
                return new ObservedValue.Constructed(made.type(), fields);
            });
        });
    }

    private static Iterator<ObservedValue> elementsOf(ObservedValue.Sequence held,
                                                      Shape.Sequence sequence,
                                                      RuleReadingContext reading, TermPath at,
                                                      List<Narrowing> along, Leaves leaves) {
        TermPath each = at == null ? null : at.element();
        return flat(indexes(held.elements().size()), index ->
                mapped(of(held.elements().get(index), sequence.element(), reading, each, along,
                        leaves), near -> {
                    List<ObservedValue> elements = new ArrayList<>(held.elements());
                    elements.set(index, near);
                    return new ObservedValue.Sequence(elements);
                }));
    }

    /** {@code along}, and the sum {@code value} is the case of at {@code at}. */
    private static List<Narrowing> narrowed(List<Narrowing> along, TermPath at,
                                            ObservedValue value) {
        if (at == null) {
            return along;
        }
        List<Narrowing> out = new ArrayList<>(along);
        out.add(new Narrowing(at.steps().size(), value));
        return out;
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

    /** The ones of {@code from} that {@code keep} says yes to, asked as they are reached. */
    private static <A> Iterator<A> filtered(Iterator<A> from, Predicate<A> keep) {
        return new Iterator<>() {
            private A next;
            private boolean ready;

            @Override
            public boolean hasNext() {
                while (!ready && from.hasNext()) {
                    A candidate = from.next();
                    if (keep.test(candidate)) {
                        next = candidate;
                        ready = true;
                    }
                }
                return ready;
            }

            @Override
            public A next() {
                if (!hasNext()) {
                    throw new NoSuchElementException();
                }
                ready = false;
                return next;
            }
        };
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
