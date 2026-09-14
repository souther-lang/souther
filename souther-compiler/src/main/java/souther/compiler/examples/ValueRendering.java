package souther.compiler.examples;

import souther.compiler.observe.Alignment;
import souther.compiler.observe.Asserted;
import souther.compiler.observe.Expectation;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.PathElement;
import souther.compiler.observe.Position;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

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

    /** What a row stated, written the way a fixture writes one. A list is its own order; what it
     *  states no order for is written in the one this settles on, as the answer beside it is. */
    String show(Asserted a) {
        return switch (a) {
            case Asserted.Value(ObservedValue v) -> show(v);
            case Asserted.Built built -> {
                List<String> names = new ArrayList<>(built.fields().keySet());
                names.sort(String::compareTo);
                if (names.equals(List.of("value")) && neutral.isNewtype(built.type())) {
                    yield built.type().name() + "(" + show(built.fields().get("value")) + ")";
                }
                List<String> out = new ArrayList<>();
                for (String name : names) {
                    out.add(name + " = " + show(built.fields().get(name)));
                }
                yield out.isEmpty() ? built.type().name()
                        : built.type().name() + " { " + String.join(", ", out) + " }";
            }
            case Asserted.Elements elements -> {
                List<String> out = new ArrayList<>();
                for (Asserted e : elements.elements()) {
                    out.add(show(e));
                }
                // A set states no order, so what it is written in is decided here.
                if (elements.stated() == Asserted.Container.SET) {
                    out.sort(String::compareTo);
                }
                String written = out.isEmpty() ? "[]" : "[ " + String.join(", ", out) + " ]";
                // A row that said which collection it wrote is shown saying it, so a mismatch between
                // a set and a list of the same elements does not read as two of the same thing.
                yield elements.stated() == Asserted.Container.SET ? "Set.fromList(" + written + ")"
                        : written;
            }
            case Asserted.Entries entries -> {
                List<String> out = new ArrayList<>();
                for (Asserted.Entry e : entries.entries()) {
                    out.add(pair(e));
                }
                out.sort(String::compareTo);
                String written = out.isEmpty() ? "[]" : "[ " + String.join(", ", out) + " ]";
                yield entries.stated() ? "Map.fromList(" + written + ")" : written;
            }
        };
    }

    /** One pair a row wrote, which is also what its place among the others is decided by. */
    private String pair(Asserted.Entry e) {
        return "(" + show(e.key()) + ", " + show(e.value()) + ")";
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

    /** A set: the elements that have a counterpart, each at the place its counterpart takes, then
     *  the ones that have none. */
    private String unordered(Alignment.Unordered set, Type position) {
        Type element = elementOf(position);
        List<String> out = new ArrayList<>();
        for (Alignment.Stood each : atTheirRank(set.written(), it -> show(it.stated()))) {
            out.add(against(each.element(), each.under(), element));
        }
        List<String> rest = new ArrayList<>();
        for (ObservedValue each : set.rest()) {
            rest.add(canonical(each, element));
        }
        rest.sort(String::compareTo);
        out.addAll(rest);
        return written(out);
    }

    /** The pairs that have a counterpart, each at the place its counterpart takes, then the rest. */
    private String entries(Alignment.Entries entries, Type position) {
        Type key = NeutralForm.open(position) instanceof Type.MapOf m ? m.key() : null;
        Type value = NeutralForm.open(position) instanceof Type.MapOf m ? m.value() : null;
        List<String> out = new ArrayList<>();
        for (Alignment.Placed each : atTheirRank(entries.written(), it -> pair(it.stated()))) {
            out.add("(" + canonical(each.entry().key(), key) + ", "
                    + against(each.entry().value(), each.under(), value) + ")");
        }
        List<String> rest = new ArrayList<>();
        for (ObservedValue.Entry each : entries.rest()) {
            rest.add("(" + canonical(each.key(), key) + ", " + canonical(each.value(), value) + ")");
        }
        rest.sort(String::compareTo);
        out.addAll(rest);
        return out.isEmpty() ? "[]" : "[ " + String.join(", ", out) + " ]";
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
                Type key = open instanceof Type.MapOf map ? map.key() : null;
                Type value = open instanceof Type.MapOf map ? map.value() : null;
                List<String> out = new ArrayList<>();
                for (ObservedValue.Entry each : m.entries()) {
                    out.add("(" + canonical(each.key(), key) + ", "
                            + canonical(each.value(), value) + ")");
                }
                out.sort(String::compareTo);
                yield out.isEmpty() ? "[]" : "[ " + String.join(", ", out) + " ]";
            }
            case ObservedValue.Sequence s -> {
                Type element = elementOf(position);
                List<String> out = new ArrayList<>();
                for (ObservedValue each : s.elements()) {
                    out.add(canonical(each, element));
                }
                if (open instanceof Type.SetOf) {
                    out.sort(String::compareTo);
                }
                yield written(out);
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

    /**
     * The answer's parts in the places the statement's take, which is the order the statement's are
     * written in.
     *
     * <p>Not the order the statement holds them in. What a row states is a value, worked out by
     * running what it wrote — so the collection it states holds its parts in whatever a table walked,
     * exactly as the answer does, and following it would put one accident where the other was.
     * Whichever order the statement is written out in is the order it is read in, so that is the one
     * the answer's parts take: the two columns line up, and neither is anybody's hash.
     *
     * <p>By what the statement's part is written as and not what the answer's is, so that two parts
     * the comparison found to be one value stand together even where they are spelled apart —
     * {@code 1.0} and {@code 1.00} are one amount and would sort to two places.
     *
     * <p>Each written once and sorted on what came back. Writing a part out is a walk of the whole
     * of it, and a comparison that asked for one every time it compared two would walk each of them
     * as many times as a sort looks at it.
     */
    private static <T> List<T> atTheirRank(List<T> written, java.util.function.Function<T, String> of) {
        List<Map.Entry<String, T>> ranked = new ArrayList<>(written.size());
        for (T each : written) {
            ranked.add(Map.entry(of.apply(each), each));
        }
        ranked.sort(Map.Entry.comparingByKey());
        List<T> out = new ArrayList<>(ranked.size());
        for (Map.Entry<String, T> each : ranked) {
            out.add(each.getValue());
        }
        return out;
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

    /** The value as a row would write it, where nothing says what its sequences are. */
    String show(ObservedValue v) {
        return switch (v) {
            case ObservedValue.Bool b -> String.valueOf(b.value());
            case ObservedValue.Integer i -> String.valueOf(i.value());
            case ObservedValue.Decimal d -> d.value().toPlainString();
            case ObservedValue.Text t -> "\"" + t.value() + "\"";
            // Written as the construction a fixture writes one with, so it is never read as the text
            // that spells it — which is the difference a row writing a date as a string is told about.
            case ObservedValue.Temporal t -> t.primitive().shown() + "(\"" + t.iso() + "\")";
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
                case PathElement.Key(Asserted key) ->
                        out.append('[').append(show(key)).append(']');
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
