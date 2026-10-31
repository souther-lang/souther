package souther.compiler.examples;

import souther.compiler.check.ValuePlaces;
import souther.compiler.cst.CstLexer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Place;
import souther.compiler.observe.Alignment;
import souther.compiler.observe.Asserted;
import souther.compiler.observe.Expectation;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.PathElement;
import souther.compiler.observe.Position;
import souther.compiler.observe.UnorderedOrder;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

/**
 * A structured value written the way a fixture writes one.
 *
 * <p>Not the encoder. An encoder writes a value as the representation it crosses a boundary in, and a
 * newtype's representation is the base it wraps — which is right for a boundary and wrong for a
 * diagnostic, where the whole question may be which of two names over one base a value wears. So a
 * mismatch is rendered from the structured value, where the name is still there to write.
 */
final class ValueRendering {

    private final NeutralForm neutral;

    ValueRendering(NeutralForm neutral) {
        this.neutral = neutral;
    }

    /**
     * What a row stated at {@code position}, written the way a fixture writes one and the way the
     * answer beside it is. A list is its own order; what it states no order for is written in the
     * one this settles on.
     *
     * <p>The position is what says where a number sits, so a set or a map the row wrote is put in
     * the order of its values by the same rule the answer is ({@link UnorderedOrder}), and the two
     * sides of a mismatch list their common parts in one order. With no position the row says
     * nothing about its type, and what it states no order for is written in the order of its text.
     */
    String show(Asserted a, Type position) {
        return switch (a) {
            case Asserted.Value(ObservedValue v) -> show(v);
            case Asserted.Built built -> {
                Map<String, Type> declared = position == null ? Map.of()
                        : neutral.fieldTypes(built.type());
                List<String> names = new ArrayList<>(built.fields().keySet());
                names.sort(String::compareTo);
                if (names.equals(List.of("value")) && neutral.isNewtype(built.type())) {
                    yield built.type().name() + "("
                            + show(built.fields().get("value"), declared.get("value")) + ")";
                }
                List<String> out = new ArrayList<>();
                for (String name : names) {
                    out.add(name + " = " + show(built.fields().get(name), declared.get(name)));
                }
                yield out.isEmpty() ? built.type().name()
                        : built.type().name() + " { " + String.join(", ", out) + " }";
            }
            case Asserted.Elements elements -> {
                Type element = elementOf(position);
                boolean set = elements.stated() == Asserted.Container.SET;
                // A set states no order, so what it is written in is decided here.
                ValuePlaces places = neutral.placesAt(element);
                List<String> out = set
                        ? inOrder(elements.elements(), e -> places.of(e), e -> show(e, element))
                        : elements.elements().stream().map(e -> show(e, element)).toList();
                String written = written(out);
                // A row that said which collection it wrote is shown saying it, so a mismatch between
                // a set and a list of the same elements does not read as two of the same thing.
                yield set ? "Set.fromList(" + written + ")" : written;
            }
            case Asserted.Entries entries -> {
                Type key = keyOf(position);
                Type value = valueOf(position);
                ValuePlaces places = neutral.placesAt(key);
                String written = written(inOrder(entries.entries(), e -> places.of(e.key()),
                        e -> pair(e, key, value)));
                yield entries.stated() ? "Map.fromList(" + written + ")" : written;
            }
        };
    }

    /** One pair a row wrote. */
    private String pair(Asserted.Entry e, Type key, Type value) {
        return "(" + show(e.key(), key) + ", " + show(e.value(), value) + ")";
    }

    /**
     * {@code parts} of a collection that states no order, each written once and put in the order
     * {@link UnorderedOrder} gives: by the place of the part where there is one, by its text where
     * not.
     */
    private static <T> List<String> inOrder(List<T> parts, Function<T, Place> placeOf,
                                            Function<T, String> textOf) {
        List<Map.Entry<T, String>> written = new ArrayList<>(parts.size());
        for (T each : parts) {
            written.add(Map.entry(each, textOf.apply(each)));
        }
        return UnorderedOrder.of(written, it -> placeOf.apply(it.getKey()), Map.Entry::getValue)
                .stream().map(Map.Entry::getValue).toList();
    }

    private static Type keyOf(Type position) {
        return position != null && NeutralForm.open(position) instanceof Type.MapOf m ? m.key() : null;
    }

    private static Type valueOf(Type position) {
        return position != null && NeutralForm.open(position) instanceof Type.MapOf m
                ? m.value() : null;
    }

    /** What a row wrote is, named as the language names it. */
    String typeShown(Asserted a) {
        return switch (a) {
            case Asserted.Value(ObservedValue v) -> typeShown(v);
            case Asserted.Built built -> built.type().name();
            case Asserted.Elements elements -> switch (elements.stated()) {
                case SET -> "a set";
                case LIST -> "a list";
                case UNSTATED -> "a collection";
            };
            case Asserted.Entries _ -> "a map";
        };
    }

    /**
     * What came out, written the way a row writes one.
     *
     * <p>{@code position} is what the behavior declares here, which is the only thing that says
     * whether a sequence is a list or a set — the same reading the comparison used, handed on rather
     * than worked out a second time. A list is its own order; a set and a map have none, so what
     * they are written in is decided ({@link #canonical}).
     */
    String show(ObservedValue v, Type position) {
        String written = canonical(v, position);
        return v instanceof ObservedValue.Sequence
                && NeutralForm.open(position) instanceof Type.SetOf
                ? "Set.fromList(" + written + ")" : written;
    }

    /**
     * What came out, written beside what a row stated and put where the correspondence says.
     *
     * <p><b>Neither side has an order to lend.</b> A map and a set state none, and a row states a
     * value rather than the way its source happened to build one: what the row wrote is run, and the
     * collection that comes back holds its parts where a table put them, exactly as the answer's
     * does. So the two look like somebody's sequences and neither is, and writing the answer in the
     * row's puts one accident where the other was.
     *
     * <p><b>The report supplies the order, because showing a value as a sequence is the report's
     * doing.</b> What has no order of its own is written in one this compiler settles on, and both
     * sides are written in it. That is not an order given to the value — nothing downstream may read
     * it as one — it is what a reader is handed instead of a hash.
     *
     * <p><b>Which of the answer's parts stands for which of the row's is still the comparison's
     * answer.</b> Each part of the answer takes the place its counterpart takes, so two parts that
     * are one value stand together even where they are spelled apart — a decimal is the amount it
     * stands for, and {@code 1.0} and {@code 1.00} would otherwise be written into two places. A
     * part with no counterpart follows the ones that have them.
     */
    String show(ObservedValue v, Type position, Alignment against) {
        String written = against(v, against, position);
        // Said as the collection it is where the position is the whole answer, which is where the
        // rendering beside it says so too. What a field holds is written as the value it is, as it
        // was before anything here read a position: which collection that is, is the row's to say
        // and is said once.
        return v instanceof ObservedValue.Sequence
                && NeutralForm.open(position) instanceof Type.SetOf
                ? "Set.fromList(" + written + ")" : written;
    }

    /**
     * What came out, each part at the place its counterpart takes, wherever the row reaches.
     *
     * <p>Carried down rather than applied at the top, because the collection a row and an answer
     * differ inside may be under a field or an element. Where the correspondence found no
     * counterpart, nothing says which part this goes with and it is written where the one order
     * puts it.
     *
     * <p>Which shape a sequence is — the value's own order, or none — the correspondence says,
     * because it was worked out where the declaration was in hand. A reader of it does not decide
     * that a second time.
     */
    private String against(ObservedValue v, Alignment against, Type position) {
        return switch (against) {
            case Alignment.Entries entries when v instanceof ObservedValue.Mapping _ ->
                    entries(entries, position);
            case Alignment.Built(Map<String, Alignment> fields)
                    when v instanceof ObservedValue.Constructed c -> constructed(c, fields);
            case Alignment.InOrder(List<Alignment> by) when v instanceof ObservedValue.Sequence s ->
                    inOrder(s, by, position);
            case Alignment.Unordered unordered when v instanceof ObservedValue.Sequence _ ->
                    unordered(unordered, position);
            case Alignment.Nothing _ -> canonical(v, position);
            // A value with no parts, and a part the correspondence lines up with nothing. Neither
            // has anything of the row's under it to put anywhere.
            case Alignment.Leaf _, Alignment.Built _, Alignment.InOrder _, Alignment.Unordered _,
                    Alignment.Entries _ -> canonical(v, position);
        };
    }

    /** A list: its own order, each element against the one standing in its place. */
    private String inOrder(ObservedValue.Sequence s, List<Alignment> by, Type position) {
        Type element = elementOf(position);
        List<String> out = new ArrayList<>();
        for (int i = 0; i < s.elements().size(); i++) {
            out.add(i < by.size() ? against(s.elements().get(i), by.get(i), element)
                    : canonical(s.elements().get(i), element));
        }
        return written(out);
    }

    /**
     * A set: the elements that have a counterpart, each at the place its counterpart takes, then
     * the ones that have none.
     *
     * <p>The answer's parts stand in the order the statement's are written in, and that order is
     * {@link UnorderedOrder}'s, the one {@link #show(Asserted, Type)} writes the statement in. It is
     * not the order the statement holds them in: what a row states is a value, worked out by running
     * what it wrote, so its collection holds its parts in whatever a table walked, exactly as the
     * answer does, and following it would put one accident where the other was. The place is the
     * answer part's, which is the counterpart's, so two parts the comparison found to be one value
     * stand together even where they are spelled apart: {@code 1.0} and {@code 1.00} are one amount.
     * Each part is written once, because writing one is a walk of the whole of it.
     */
    private String unordered(Alignment.Unordered set, Type position) {
        Type element = elementOf(position);
        ValuePlaces places = neutral.placesAt(element);
        List<String> out = new ArrayList<>();
        for (Alignment.Stood each : UnorderedOrder.of(set.written(),
                it -> places.of(it.element()), it -> show(it.stated(), element))) {
            out.add(against(each.element(), each.under(), element));
        }
        out.addAll(inOrder(set.rest(), places::of, it -> canonical(it, element)));
        return written(out);
    }

    /** The pairs that have a counterpart, each at the place its counterpart takes, then the rest. */
    private String entries(Alignment.Entries entries, Type position) {
        Type key = keyOf(position);
        Type value = valueOf(position);
        ValuePlaces places = neutral.placesAt(key);
        List<String> out = new ArrayList<>();
        for (Alignment.Placed each : UnorderedOrder.of(entries.written(),
                it -> places.of(it.entry().key()), it -> pair(it.stated(), key, value))) {
            out.add("(" + canonical(each.entry().key(), key) + ", "
                    + against(each.entry().value(), each.under(), value) + ")");
        }
        out.addAll(inOrder(entries.rest(), it -> places.of(it.key()),
                it -> "(" + canonical(it.key(), key) + ", " + canonical(it.value(), value) + ")"));
        return written(out);
    }

    /** The fields, each beside the one the row wrote under that name where it wrote one. */
    private String constructed(ObservedValue.Constructed c, Map<String, Alignment> fields) {
        Map<String, Type> declared = neutral.fieldTypes(c.type());
        ObservedValue inner = c.field("value");
        if (inner != null && neutral.isNewtype(c.type()) && c.fields().size() == 1) {
            Alignment under = fields.get("value");
            Type held = declared.get("value");
            return c.type().name() + "("
                    + (under == null ? canonical(inner, held) : against(inner, under, held)) + ")";
        }
        List<String> names = new ArrayList<>(c.fields().keySet());
        names.sort(String::compareTo);
        List<String> out = new ArrayList<>();
        for (String name : names) {
            Alignment under = fields.get(name);
            Type held = declared.get(name);
            out.add(name + " = " + (under == null ? canonical(c.fields().get(name), held)
                    : against(c.fields().get(name), under, held)));
        }
        return out.isEmpty() ? c.type().name()
                : c.type().name() + " { " + String.join(", ", out) + " }";
    }

    /**
     * A value nothing states an order for, written the one way.
     *
     * <p>What {@link #show(ObservedValue)} does, except that what holds no order of its own is put
     * in the order it is written out in rather than the order the value happens to hold it. That
     * order says nothing — nobody chose it and nothing may read it as a fact about the value — and
     * what it is for is that two runs of one report read alike.
     *
     * <p><b>Which of them hold no order is the position's answer and not the value's.</b> What came
     * out of a run holds a list and a set the one way, and the declaration is the only thing that
     * says which this is: asked of the value, a set would be written in whatever its table walked
     * and the number would be back in the report. Where nothing declares the position, nothing here
     * is in a position to put it in an order either, and it is written as it stands.
     *
     * <p>All the way down. A pair nobody stated may hold a set of its own, and leaving that one as
     * the run's table walked it puts the number back one level below where it was taken out.
     */
    private String canonical(ObservedValue v, Type position) {
        Type open = position == null ? null : NeutralForm.open(position);
        return switch (v) {
            case ObservedValue.Mapping m -> {
                Type key = keyOf(position);
                Type value = valueOf(position);
                ValuePlaces places = neutral.placesAt(key);
                yield written(inOrder(m.entries(), each -> places.of(each.key()),
                        each -> "(" + canonical(each.key(), key) + ", "
                                + canonical(each.value(), value) + ")"));
            }
            case ObservedValue.Sequence s -> {
                Type element = elementOf(position);
                ValuePlaces places = neutral.placesAt(element);
                yield written(open instanceof Type.SetOf
                        ? inOrder(s.elements(), each -> places.of(each),
                                each -> canonical(each, element))
                        : s.elements().stream().map(each -> canonical(each, element)).toList());
            }
            case ObservedValue.Constructed c -> {
                Map<String, Type> declared = neutral.fieldTypes(c.type());
                ObservedValue inner = c.field("value");
                if (inner != null && neutral.isNewtype(c.type()) && c.fields().size() == 1) {
                    yield c.type().name() + "(" + canonical(inner, declared.get("value")) + ")";
                }
                List<String> names = new ArrayList<>(c.fields().keySet());
                names.sort(String::compareTo);
                List<String> out = new ArrayList<>();
                for (String name : names) {
                    out.add(name + " = " + canonical(c.fields().get(name), declared.get(name)));
                }
                yield out.isEmpty() ? c.type().name()
                        : c.type().name() + " { " + String.join(", ", out) + " }";
            }
            default -> show(v);
        };
    }

    /** What a sequence at {@code position} holds, or nothing where the position says nothing. */
    private static Type elementOf(Type position) {
        Type open = position == null ? null : NeutralForm.open(position);
        return switch (open) {
            case Type.ListOf l -> l.element();
            case Type.SetOf s -> s.element();
            case null, default -> null;
        };
    }

    /** A sequence written out. Which collection it is is said where the whole answer is written and
     *  not at every element of it, which is how it read before a position was carried down here. */
    private static String written(List<String> out) {
        return out.isEmpty() ? "[]" : "[ " + String.join(", ", out) + " ]";
    }

    /** What came out is, named as the language names it, at the position that says what it is. */
    String typeShown(ObservedValue v, Type position) {
        return typeShown(v, Position.at(position));
    }

    /** The same, where what reads the value is a place rather than a written type. */
    String typeShown(ObservedValue v, Position position) {
        if (v instanceof ObservedValue.Sequence) {
            return position.opened() instanceof Position.At(Type type) && type instanceof Type.SetOf
                    ? "a set" : "a list";
        }
        return typeShown(v);
    }

    /** What the row stated, named as the language names it. */
    String typeShown(Expectation.Asserts stated) {
        return switch (stated) {
            case Expectation.TheValue(Asserted value) -> typeShown(value);
            case Expectation.TheCase(TypeSymbol name) -> name.name();
        };
    }

    /** The value as a row would write it, where nothing says what its sequences are — a decimal in
     *  exponent notation past a thousand digits ({@link ExactRatio#spelledBounded}), since this is a
     *  diagnostic a reader reads and not source pasted back. */
    String show(ObservedValue v) {
        return switch (v) {
            case ObservedValue.Bool b -> String.valueOf(b.value());
            case ObservedValue.Integer i -> String.valueOf(i.value());
            case ObservedValue.Decimal d -> ExactRatio.spelledBounded(d.value());
            case ObservedValue.Text t -> CstLexer.literalOf(t.value());
            // Written as the construction a fixture writes one with, so it is never read as the text
            // that spells it — which is the difference a row writing a date as a string is told about.
            case ObservedValue.Temporal t ->
                    t.primitive().shown() + "(" + CstLexer.literalOf(t.iso()) + ")";
            case ObservedValue.Unit u -> u.type().name();
            case ObservedValue.Absent _ -> "None";
            case ObservedValue.Constructed c -> constructed(c);
            case ObservedValue.Sequence s -> {
                List<String> out = new ArrayList<>();
                for (ObservedValue e : s.elements()) {
                    out.add(show(e));
                }
                yield out.isEmpty() ? "[]" : "[ " + String.join(", ", out) + " ]";
            }
            case ObservedValue.Mapping m -> {
                List<String> out = new ArrayList<>();
                for (ObservedValue.Entry e : m.entries()) {
                    out.add("(" + show(e.key()) + ", " + show(e.value()) + ")");
                }
                yield out.isEmpty() ? "[]" : "[ " + String.join(", ", out) + " ]";
            }
            case ObservedValue.Unknown u -> "?(" + u.reason() + ")";
            case ObservedValue.Truncated _ -> "?";
        };
    }

    private String constructed(ObservedValue.Constructed c) {
        ObservedValue inner = c.field("value");
        if (inner != null && neutral.isNewtype(c.type()) && c.fields().size() == 1) {
            return c.type().name() + "(" + show(inner) + ")";
        }
        // A structured value holds its fields by name and not in an order, so the writer puts them in
        // one: two renderings of one value have to read alike, and two runs have to agree. Lexical,
        // and it says nothing — a diagnostic would rather show a record in the order it was declared,
        // and a structured value cannot be asked what that order was. Nothing may read this order as
        // the declaration's.
        List<String> names = new ArrayList<>(c.fields().keySet());
        names.sort(String::compareTo);
        List<String> out = new ArrayList<>();
        for (String name : names) {
            out.add(name + " = " + show(c.fields().get(name)));
        }
        return out.isEmpty() ? c.type().name()
                : c.type().name() + " { " + String.join(", ", out) + " }";
    }

    /**
     * The place inside a value a difference is at, as a reader of this compiler's reports reads one.
     *
     * <p>Written here and not carried as text. What names an entry is the key it was found by, and a
     * key is written the way any other value this reports is — so spelling a path needs what spells a
     * value, and a path spelled anywhere else would be a second answer to how a value is written.
     */
    String shown(List<PathElement> path) {
        StringBuilder out = new StringBuilder("$");
        for (PathElement step : path) {
            switch (step) {
                case PathElement.Field(String name) -> out.append('.').append(name);
                case PathElement.Index(int at) -> out.append('[').append(at).append(']');
                // A key is found by what it is, and no position declares the one it stands at.
                case PathElement.Key(Asserted key) ->
                        out.append('[').append(show(key, null)).append(']');
            }
        }
        return out.toString();
    }

    /**
     * What the value is, named as the language names it — what a mismatch says when the two sides
     * differ by their type rather than by their contents.
     */
    String typeShown(ObservedValue v) {
        Type.Prim primitive = v.primitive();
        if (primitive != null) {
            return primitive.shown();   // the one table a primitive is spelled from
        }
        return switch (v) {
            case ObservedValue.Unit u -> u.type().name();
            case ObservedValue.Constructed c -> c.type().name();
            case ObservedValue.Absent _ -> "None";
            case ObservedValue.Sequence _ -> "a collection";
            case ObservedValue.Mapping _ -> "a map";
            default -> "unread";
        };
    }
}
