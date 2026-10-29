package souther.compiler.partition;

import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.Shape;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.PieceDemand;
import souther.compiler.observe.Figure;
import souther.compiler.observe.ObservedValue;
import souther.compiler.semantics.CaseMapping;
import souther.compiler.types.Type;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.IntPredicate;
import java.util.function.Predicate;
import java.util.function.Supplier;

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

        /** What a list becomes beyond its elements moved one at a time: nothing, unless a step
         *  adds to the list itself. */
        default Iterator<ObservedValue> longer(ObservedValue.Sequence unusedHeld,
                                               Shape.Sequence unusedSequence, TermPath unusedAt) {
            return none();
        }
    }

    private static final Leaves WHOLE_NUMBERS = (prim, leaf, _, _, _) ->
            prim == Type.Prim.INT && leaf instanceof ObservedValue.Integer whole
                    ? stepsOf(whole) : none();

    /**
     * A whole number is one apart from the next, and a decimal is one unit of its own scale apart
     * from the next it can write; the other leaves have no such step. Not {@link #WHOLE_NUMBERS}:
     * that is where a number seen taking a value is moved, and a decimal there has no value directly
     * beside it. This is where a value is wanted that is not the one in hand, and any value a
     * decimal can write at its scale is one.
     */
    private static final Leaves ONE_UNIT = (prim, leaf, _, _, _) -> switch (leaf) {
        case ObservedValue.Integer whole when prim == Type.Prim.INT -> stepsOf(whole);
        case ObservedValue.Decimal decimal when prim == Type.Prim.DECIMAL -> unitsOf(decimal);
        default -> none();
    };

    /** The values one step from {@code value}, standing at a position of {@code type}. */
    static Iterator<ObservedValue> of(ObservedValue value, Type type, RuleReadingContext reading) {
        return of(value, type, reading, null, List.of(), WHOLE_NUMBERS);
    }

    /**
     * The values a unit away from {@code value}, standing at a position of {@code type}: the next
     * whole number either way, and the next decimal of its scale either way. For a search that
     * wants a value other than a representative of the type, which a decimal's neighbours
     * ({@link #of}) are not.
     */
    static Iterator<ObservedValue> oneUnitFrom(ObservedValue value, Type type,
                                               RuleReadingContext reading) {
        return of(value, type, reading, null, List.of(), ONE_UNIT);
    }

    /**
     * The values {@code value} becomes where a list it holds, or is, has one more element: a value
     * a run took at a position of the element's type ({@code ranWith}), and after those a value
     * {@code stoodFor} offers for the type, put after the elements it has, and everything else
     * stays as it was.
     *
     * <p>For a list the classes divide no way, which holds only what the rows written ran with and
     * has no element to move a number of. What an element can be is then what the rows of the
     * module ran a position of its type with, and where none did, what stands for the type.
     * Handed over one at a time, a list at a time in the order the value is walked.
     */
    static Iterator<ObservedValue> grown(ObservedValue value, Type type, RuleReadingContext reading,
                                         InputsRowsRanWith ranWith,
                                         Function<Type, Iterator<ObservedValue>> stoodFor) {
        return withAnElement(value, type, reading, ranWith, stoodFor, Lists.ANY, Put.AFTER, null);
    }

    /**
     * How many elements the list {@code within} names holds in {@code value}, or the lists it
     * names between them where the location goes through the elements of another. None where the
     * value has no such list.
     */
    static int heldAt(ObservedValue value, Type type, RuleReadingContext reading, TermPath within) {
        return heldAt(value, type, reading, new TermPath(within.head(), List.of()), within);
    }

    private static int heldAt(ObservedValue value, Type type, RuleReadingContext reading,
                              TermPath at, TermPath within) {
        if (value.unread() != null || at.steps().size() > within.steps().size()
                || !within.steps().subList(0, at.steps().size()).equals(at.steps())) {
            return 0;
        }
        var source = reading.source();
        TypeView view = TypeView.of(type, source.inners(), source.symbols(), source.kinds(),
                source.sums());
        ObservedValue inside = ObservedValue.wearing(view.wrappers(), value);
        if (inside == null || inside.unread() != null) {
            return 0;
        }
        return switch (view.shape()) {
            case Shape.Product product -> {
                int n = 0;
                if (inside instanceof ObservedValue.Constructed made
                        && made.type().equals(product.name())) {
                    for (Map.Entry<String, Type> field : product.fields().entrySet()) {
                        ObservedValue held = made.field(field.getKey());
                        if (held != null) {
                            n += heldAt(held, field.getValue(), reading,
                                    at.then(field.getKey()), within);
                        }
                    }
                }
                yield n;
            }
            case Shape.Sequence sequence -> {
                if (!(inside instanceof ObservedValue.Sequence held)) {
                    yield 0;
                }
                if (at.equals(within)) {
                    yield held.elements().size();
                }
                int n = 0;
                for (ObservedValue each : held.elements()) {
                    n += heldAt(each, sequence.element(), reading, at.element(), within);
                }
                yield n;
            }
            case Shape.Sum sum -> inside instanceof ObservedValue.Constructed made
                    && sum.reaches().cases().contains(made.type())
                    ? heldAt(inside, Type.ref(made.type()), reading, at, within) : 0;
            case Shape.Optional optional -> inside instanceof ObservedValue.Absent ? 0
                    : heldAt(inside, optional.element(), reading, at, within);
            case Shape.Scalar _, Shape.Mapping _, Shape.Unit _, Shape.Unresolved _, Shape.Cases _,
                 Shape.Tuple _, Shape.Function _, Shape.Uninhabited _, Shape.Bottom _,
                 Shape.Erroneous _, Shape.Undecided _ -> 0;
        };
    }

    /** Where a list that grows takes its new element. */
    enum Put {

        /** After the elements it has. */
        AFTER,

        /** After them, and then before them: what a list does with an element it is handed first
         *  is not what it does with one it is handed last. */
        BEFORE_AND_AFTER
    }

    /** Which of the lists a value holds are the ones that grow. */
    enum Lists {

        /** Every one. */
        ANY,

        /** The ones that hold an element: grown, they hold two or more. */
        HOLDING_SOME,

        /** The ones that hold nothing: grown, they hold one. */
        HOLDING_NONE;

        boolean admits(int elements) {
            return switch (this) {
                case ANY -> true;
                case HOLDING_SOME -> elements > 0;
                case HOLDING_NONE -> elements == 0;
            };
        }
    }

    /**
     * {@link #grown}, the new element put as {@code where} says in the lists {@code which} names.
     * The same wherever the list stands: a list in a field of a record or in an element of another
     * list takes its new element where a list that is the value itself does.
     */
    static Iterator<ObservedValue> grown(ObservedValue value, Type type, RuleReadingContext reading,
                                         InputsRowsRanWith ranWith,
                                         Function<Type, Iterator<ObservedValue>> stoodFor,
                                         Put where, Lists which) {
        return withAnElement(value, type, reading, ranWith, stoodFor, which, where, null);
    }

    /**
     * {@link #grown}, in the one list {@code within} names and no other: the list a walk goes over,
     * where a list that is not it, however deep, is one no step of the walk reads.
     *
     * @param within a location in the position {@code value} stands at, rooted at that position's
     *               parameter
     */
    static Iterator<ObservedValue> grownWithin(ObservedValue value, Type type,
                                               RuleReadingContext reading,
                                               InputsRowsRanWith ranWith,
                                               Function<Type, Iterator<ObservedValue>> stoodFor,
                                               Put where, Lists which, TermPath within) {
        return withAnElement(value, type, reading, ranWith, stoodFor, which, where, within);
    }

    /**
     * The values {@code value} becomes where a list it holds, or is, that holds nothing has an
     * element a value {@code stoodFor} offers for the type: a list with something in it is left as
     * it is, and everything else stays as it was.
     *
     * <p>One level deeper in the lists and no longer in any of them, which is what separates a
     * value that goes on from one that only gets bigger. A type whose lists are all filled has
     * nothing left to fill, and the values asked for one after another come to an end.
     */
    static Iterator<ObservedValue> populated(ObservedValue value, Type type,
                                             RuleReadingContext reading,
                                             Function<Type, Iterator<ObservedValue>> stoodFor) {
        return withAnElement(value, type, reading, InputsRowsRanWith.NONE, stoodFor,
                Lists.HOLDING_NONE, Put.AFTER, null);
    }

    private static Iterator<ObservedValue> withAnElement(
            ObservedValue value, Type type, RuleReadingContext reading, InputsRowsRanWith ranWith,
            Function<Type, Iterator<ObservedValue>> stoodFor, Lists which, Put where,
            TermPath within) {
        TermPath root = within == null ? null : new TermPath(within.head(), List.of());
        return of(value, type, reading, root, List.of(), new Leaves() {

            @Override
            public Iterator<ObservedValue> beside(Type.Prim prim, ObservedValue leaf, TermPath at,
                                                  List<Narrowing> along, TypeView view) {
                return none();
            }

            @Override
            public Iterator<ObservedValue> longer(ObservedValue.Sequence held,
                                                  Shape.Sequence sequence, TermPath at) {
                if (!which.admits(held.elements().size())
                        || (within != null && !within.equals(at))) {
                    return none();
                }
                // One of the rows' and one of the type's in turn, so that however many values the
                // rows ran with, the type's are reached within the runs the search is given. The
                // type's are asked for when the second is.
                return flat(filtered(alternating(ranWith.of(sequence.element()).iterator(),
                                () -> stoodFor.apply(sequence.element())),
                                new HashSet<ObservedValue>()::add),
                        more -> {
                            List<ObservedValue> after = new ArrayList<>(held.elements());
                            after.add(more);
                            ObservedValue.Sequence appended = new ObservedValue.Sequence(after);
                            if (where == Put.AFTER || held.elements().isEmpty()) {
                                return List.<ObservedValue>of(appended).iterator();
                            }
                            List<ObservedValue> before = new ArrayList<>();
                            before.add(more);
                            before.addAll(held.elements());
                            ObservedValue.Sequence prepended = new ObservedValue.Sequence(before);
                            return prepended.equals(appended)
                                    ? List.<ObservedValue>of(appended).iterator()
                                    : List.<ObservedValue>of(appended, prepended).iterator();
                        });
            }
        });
    }

    /**
     * The values {@code value} becomes where one element of a list it holds is another value a run
     * took at a position of the element's type ({@code ranWith}), one element at a time, and
     * everything else stays as it was.
     *
     * <p>For a walk over a list a row holds, where what the step does with one element and what it
     * does with another is the difference a rewrite of the walk is seen by: a list as long as the
     * row's, with an element the rows speak of elsewhere in the place of one of its own.
     */
    static Iterator<ObservedValue> withAnElementChanged(ObservedValue value, Type type,
                                                        RuleReadingContext reading,
                                                        InputsRowsRanWith ranWith) {
        return of(value, type, reading, null, List.of(), new Leaves() {

            @Override
            public Iterator<ObservedValue> beside(Type.Prim prim, ObservedValue leaf, TermPath at,
                                                  List<Narrowing> along, TypeView view) {
                return none();
            }

            @Override
            public Iterator<ObservedValue> longer(ObservedValue.Sequence held,
                                                  Shape.Sequence sequence, TermPath unusedAt) {
                List<ObservedValue> others = ranWith.of(sequence.element());
                // A list at a time, as the search asks: the element changed, and then the value
                // it is changed to, so that a long list is copied once for each candidate taken
                // and not once for each there could be.
                return flat(indexes(held.elements().size()), at -> mapped(
                        filtered(others.iterator(),
                                other -> !other.equals(held.elements().get(at))),
                        other -> {
                            List<ObservedValue> elements = new ArrayList<>(held.elements());
                            elements.set(at, other);
                            return new ObservedValue.Sequence(elements);
                        }));
            }
        });
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
                                            Consumer<Figure> stoppedAt) {
        // What the row holds that a piece is taken from is the same wherever a demand is met, so
        // it is read the first time it is asked for and not again.
        Map<PieceDemand, List<String>> held = new HashMap<>();
        return of(value, type, reading, TermPath.of(parameter), List.of(),
                (prim, leaf, at, along, view) -> {
            if (prim != Type.Prim.STRING || !(leaf instanceof ObservedValue.Text text)) {
                return none();
            }
            List<PieceDemand> here = demands.stream()
                    .filter(each -> standsAt(each.position(), at, along)).toList();
            Set<String> offered = new HashSet<>(List.of(text.value()));
            Iterator<String> strings = flat(here.iterator(), demand -> flat(
                    shapesOf(text.value(), demand, held.computeIfAbsent(demand,
                            each -> heldBy(each, reading, row, stoppedAt)), stoppedAt)
                            .iterator(),
                    shape -> made(Partitions.stringsPartedInto(view, reading, demand.attempted(),
                            demand.separator(), demand.through(), shape), stoppedAt)));
            return mapped(filtered(strings, offered::add), ObservedValue.Text::new);
        });
    }

    /**
     * The values {@code value} becomes where a string it holds has one piece more at one of
     * {@code separators}: an empty piece after it, an empty piece before it, and the string again
     * after it. Everything else stays as it was.
     *
     * <p>For a walk over the pieces of a string a body parts, which a row is handed more elements
     * of only through the string: a string of one piece is walked no further than its first
     * element. Whether the string so written is one its type admits is the candidate's check to
     * say, as it is for every candidate.
     */
    static Iterator<ObservedValue> withAPieceMore(ObservedValue value, Type type,
                                                  RuleReadingContext reading, String parameter,
                                                  List<String> separators) {
        return of(value, type, reading, TermPath.of(parameter), List.of(),
                (prim, leaf, _, _, _) -> {
            if (prim != Type.Prim.STRING || !(leaf instanceof ObservedValue.Text text)) {
                return none();
            }
            Set<String> offered = new HashSet<>(List.of(text.value()));
            List<String> strings = new ArrayList<>();
            for (String separator : separators) {
                strings.add(text.value() + separator);
                strings.add(separator + text.value());
                strings.add(text.value() + separator + text.value());
            }
            return mapped(filtered(strings.iterator(), offered::add), ObservedValue.Text::new);
        });
    }

    /** The strings made, and the figure the making was refused at where it was. */
    private static Iterator<String> made(Partitions.StringsPartedInto.Parted parted,
                                         Consumer<Figure> stoppedAt) {
        return switch (parted) {
            case Partitions.StringsPartedInto.StringsMade made -> made.strings().iterator();
            case Partitions.StringsPartedInto.StringsNotMade refused -> {
                refused.refused().ifPresent(by -> stoppedAt.accept(Partitions.figureOf(by)));
                yield none();
            }
        };
    }

    /**
     * The strings of {@code row} a piece for {@code demand} may be made into: the ones that hold
     * nowhere the string is parted and that the newtype admits.
     *
     * <p>Strings of the other inputs, which are looked up against the pieces of the string once it
     * has been made into what is parted, so strings that string's pieces are made into and not
     * pieces of the input ({@link PieceShape.MadeInto}).
     *
     * <p>Read only as far as it takes to know the figure is reached: one string past it says so, and
     * the rest of the row is not asked.
     */
    private static List<String> heldBy(PieceDemand demand, RuleReadingContext reading,
                                       List<ObservedValue> row, Consumer<Figure> stoppedAt) {
        CompositionBudget taken = CompositionBudget.STRINGS_OF_THE_ROW_A_PIECE_IS_TAKEN_FROM;
        int most = taken.maximum();
        Set<String> held = new LinkedHashSet<>();
        for (ObservedValue each : row) {
            boolean more = eachText(each, text -> {
                if (text.codePoints().noneMatch(part -> part == demand.separator())
                        && Partitions.pieceAdmits(demand.attempted(), reading, text, stoppedAt)) {
                    held.add(text);
                }
                return held.size() <= most;
            });
            if (!more) {
                break;
            }
        }
        if (held.size() > most) {
            stoppedAt.accept(taken.figure());
        }
        return held.stream().limit(most).toList();
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
    private static List<List<PieceShape>> shapesOf(String seen, PieceDemand demand,
                                                   List<String> held, Consumer<Figure> stoppedAt) {
        CompositionBudget budget = CompositionBudget.PIECES_A_STRING_IS_PUT_TOGETHER_OF;
        // The pieces of the string as it is parted, which is where it is made into the separator
        // and not where it is written as one.
        List<String> pieces = partsOf(seen, Partitions.partsAt(demand.separator(),
                demand.through()));
        List<List<PieceShape>> out = new ArrayList<>();
        if (pieces.size() <= budget.maximum()) {
            for (int changed = 0; changed < pieces.size(); changed++) {
                out.add(changing(pieces, changed, new PieceShape.AnyTheTypeAdmits()));
            }
            for (String text : held) {
                for (int changed = 0; changed < pieces.size(); changed++) {
                    // The string itself first where the conversions leave it as it is: it is the
                    // string of the input that is made into it which anybody would write, and the
                    // strings made into it besides are what the meet is left to find if it is not
                    // one the input admits.
                    if (demand.through() != CaseMapping.NONE
                            && Partitions.isUnchangedBy(text, demand.through())) {
                        out.add(changing(pieces, changed, new PieceShape.AsSeen(text)));
                    }
                    out.add(changing(pieces, changed, new PieceShape.MadeInto(text)));
                }
            }
        } else {
            stoppedAt.accept(budget.figure());
        }
        if (pieces.size() + 1 > budget.maximum()) {
            stoppedAt.accept(budget.figure());
        }
        for (int count = 1; count <= Math.min(pieces.size() + 1, budget.maximum()); count++) {
            out.add(Collections.nCopies(count, new PieceShape.AnyTheTypeAdmits()));
        }
        return out;
    }

    /** {@code pieces} as they were seen, but for the one at {@code changed}, which is
     *  {@code to}. */
    private static List<PieceShape> changing(List<String> pieces, int changed, PieceShape to) {
        List<PieceShape> shape = new ArrayList<>();
        for (int at = 0; at < pieces.size(); at++) {
            shape.add(at == changed ? to : new PieceShape.AsSeen(pieces.get(at)));
        }
        return shape;
    }

    /**
     * Every string {@code value} holds, wherever in it, handed to {@code goOn} one at a time until
     * it says to stop — and whether it did not.
     */
    private static boolean eachText(ObservedValue value, Predicate<String> goOn) {
        switch (value) {
            case ObservedValue.Text text -> {
                return goOn.test(text.value());
            }
            case ObservedValue.Constructed made -> {
                for (ObservedValue each : made.fields().values()) {
                    if (!eachText(each, goOn)) {
                        return false;
                    }
                }
            }
            case ObservedValue.Sequence held -> {
                for (ObservedValue each : held.elements()) {
                    if (!eachText(each, goOn)) {
                        return false;
                    }
                }
            }
            case ObservedValue.Mapping held -> {
                for (ObservedValue.Entry entry : held.entries()) {
                    if (!eachText(entry.key(), goOn) || !eachText(entry.value(), goOn)) {
                        return false;
                    }
                }
            }
            default -> { }
        }
        return true;
    }

    /** {@code text} cut at every code point {@code parts} says it is parted at. */
    private static List<String> partsOf(String text, IntPredicate parts) {
        List<String> pieces = new ArrayList<>();
        StringBuilder piece = new StringBuilder();
        text.codePoints().forEach(each -> {
            if (parts.test(each)) {
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
                    ? flat(List.of(elementsOf(held, sequence, reading, at, along, leaves),
                            leaves.longer(held, sequence, at)).iterator(), Function.identity())
                    : none();
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

    private static Iterator<ObservedValue> unitsOf(ObservedValue.Decimal decimal) {
        // A decimal written to more places than the host can step by one of is one with no unit
        // step to offer.
        try {
            BigDecimal unit = BigDecimal.ONE.movePointLeft(Math.max(decimal.value().scale(), 0));
            return List.<ObservedValue>of(new ObservedValue.Decimal(decimal.value().add(unit)),
                    new ObservedValue.Decimal(decimal.value().subtract(unit))).iterator();
        } catch (ArithmeticException tooWide) {
            return none();
        }
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
    static <A> Iterator<A> filtered(Iterator<A> from, Predicate<A> keep) {
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
    static <A, B> Iterator<B> flat(Iterator<A> outer, Function<A, Iterator<B>> how) {
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

    /**
     * The elements of {@code first} and of {@code second} one from each in turn, {@code first}'s
     * first; what is left of the longer one after the shorter is used up. {@code second} is made
     * the first time it is wanted.
     */
    private static <A> Iterator<A> alternating(Iterator<A> first, Supplier<Iterator<A>> second) {
        return new Iterator<>() {
            private Iterator<A> later;

            private boolean firstsTurn = true;

            @Override
            public boolean hasNext() {
                return first.hasNext() || later().hasNext();
            }

            @Override
            public A next() {
                if (!hasNext()) {
                    throw new NoSuchElementException();
                }
                boolean fromFirst = first.hasNext() && (firstsTurn || !later().hasNext());
                firstsTurn = !fromFirst;
                return fromFirst ? first.next() : later().next();
            }

            private Iterator<A> later() {
                if (later == null) {
                    later = second.get();
                }
                return later;
            }
        };
    }

    private NearbyValues() {}
}
