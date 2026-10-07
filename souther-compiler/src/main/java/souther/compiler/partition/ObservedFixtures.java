package souther.compiler.partition;

import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.Shape;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.TermPath;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeReachName;
import souther.compiler.types.TypeSymbol;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.SequencedMap;
import java.util.Set;

/**
 * A value the boundary built, written as a fixture that builds it again.
 *
 * <p>The way back from what was built to what a row can carry. A row is text and a tree
 * ({@link FixtureTemplate}), and what the boundary hands back is neither: it is the value, with
 * nothing of how it was written. So what a position of a built value is, where another value is to
 * be written holding it, is written here from the value and the type the reading exposes at the
 * position, and nowhere else.
 *
 * <p>Nothing here evaluates anything. A value a module states is whatever the module says it is,
 * and the boundary has already said that by building it; what is left is spelling a value that is
 * in hand. Each part is spelled by the factory every other writer of that part uses, so a value
 * written here is written the way the same value composed anywhere else is — which is what lets two
 * of them be compared by their text ({@link Witnesses#holding}).
 *
 * <p>Two values the language takes for one come out as one text. The fields of a record go in the
 * order its declaration writes them, a set's elements and a map's entries in the order of their
 * own text, and a decimal at its fewest digits. A list keeps the order it had, since that order is
 * the value.
 *
 * <p>Not every value can be written. What an observation could not read back or a limit stopped is
 * no value at all, a name the module cannot reach cannot be written by it, and a decimal far enough
 * from an ordinary one has no literal in the language's grammar. Each of those comes back as why,
 * and none of them as a value standing in for the one that was built.
 */
final class ObservedFixtures {

    /** What writing a value came to: the value written, or why it could not be. */
    sealed interface Writing<T> {

        record Written<T>(T value) implements Writing<T> {}

        record NotWritable<T>(String why) implements Writing<T> {}
    }

    /**
     * What stands at each of {@code paths} in {@code built}, the value the boundary built for the
     * parameter they are under, written as fixtures.
     *
     * <p>One value at each. A path read at no value of the one built, or at as many values as a
     * container holds, is a position that has no one value to hand over, and is said as that.
     */
    static Writing<Map<TermPath, FixtureTemplate>> at(BehaviorInputs inputs,
                                                     ObservedValue built, Set<TermPath> paths,
                                                     RuleReadingContext reading) {
        Map<TermPath, FixtureTemplate> out = new LinkedHashMap<>();
        for (TermPath path : paths) {
            if (!(inputs.observedAt(built, path)
                    instanceof WalkResult.Reached<List<BehaviorInputs.ObservedAt>>(var found))) {
                return new Writing.NotWritable<>(
                        "`" + path + "` is not a position the value built has");
            }
            if (found.size() != 1) {
                return new Writing.NotWritable<>(found.isEmpty()
                        ? "nothing stands at `" + path + "` in the value built"
                        : "`" + path + "` is at each of " + found.size()
                                + " elements of the value built, which is no one value");
            }
            BehaviorInputs.ObservedAt one = found.getFirst();
            switch (of(one.value(), one.type(), reading)) {
                case Writing.Written<FixtureTemplate>(FixtureTemplate written) ->
                        out.put(path, written);
                case Writing.NotWritable<FixtureTemplate>(String why) -> {
                    return new Writing.NotWritable<>(
                            "the value built at `" + path + "` cannot be written: " + why);
                }
            }
        }
        return new Writing.Written<>(out);
    }

    /** {@code value}, standing at a position the reading exposes as {@code type}, written as a
     *  fixture. */
    static Writing<FixtureTemplate> of(ObservedValue value, Type type, RuleReadingContext reading) {
        if (value.unread() != null) {
            return unread(value);
        }
        RuleReadingSource source = reading.source();
        TypeView view = TypeView.of(type, source.inners(), source.symbols(), source.kinds(),
                source.sums());
        // The names the position wears are the position's, and come off the value the one way a
        // walk into it takes them off. What is under them is written by the shape, and the names
        // go back on by the one rule that puts them on every value a row writes.
        List<TypeReachName.Written> worn;
        switch (WornNames.of(view.wrappers(), source)) {
            case WornNames.Spelled spelled -> worn = spelled.names();
            case WornNames.Unwritable unwritable -> {
                return new Writing.NotWritable<>(unwritable.why());
            }
        }
        // Every name the position wears, or no value of the position: putting a name back on a
        // value that did not wear it would write a value the boundary did not build.
        ObservedValue inside = Classifier.wearing(view.wrappers(), value);
        if (inside == null) {
            return notOf();
        }
        if (inside.unread() != null) {
            return unread(inside);
        }
        return switch (bare(inside, view.shape(), reading)) {
            case Writing.Written<FixtureTemplate>(FixtureTemplate written) ->
                    new Writing.Written<>(RepresentativeSource.under(worn, written));
            case Writing.NotWritable<FixtureTemplate> no -> no;
        };
    }

    /** {@code value} as a value of {@code shape}, with no name on it. */
    private static Writing<FixtureTemplate> bare(ObservedValue value, Shape shape,
                                                 RuleReadingContext reading) {
        return switch (shape) {
            case Shape.Scalar scalar -> scalar(value, scalar.prim());
            case Shape.Unit unit -> value instanceof ObservedValue.Unit(TypeSymbol made)
                    && made.equals(unit.name())
                    ? unitCase(made, reading) : notOf();
            case Shape.Product product -> value instanceof ObservedValue.Constructed made
                    && made.type().equals(product.name())
                    ? record(made, product, reading) : notOf();
            // The case the value is, which the value says and the position does not: a sum is
            // written as one of its cases.
            case Shape.Sum sum -> {
                TypeSymbol made = switch (value) {
                    case ObservedValue.Unit unit -> unit.type();
                    case ObservedValue.Constructed constructed -> constructed.type();
                    default -> null;
                };
                yield made != null && sum.reaches().cases().contains(made)
                        ? of(value, Type.ref(made), reading) : notOf();
            }
            case Shape.Sequence sequence -> value instanceof ObservedValue.Sequence(var elements)
                    ? sequence(elements, sequence, reading) : notOf();
            case Shape.Mapping mapping -> value instanceof ObservedValue.Mapping(var entries)
                    ? mapping(entries, mapping, reading) : notOf();
            // A present optional is the value it holds, written as a fixture writes it.
            case Shape.Optional optional -> value instanceof ObservedValue.Absent
                    ? new Writing.Written<>(FixtureTemplate.none())
                    : of(value, optional.element(), reading);
            case Shape.Unresolved _, Shape.Cases _, Shape.Tuple _, Shape.Function _,
                 Shape.Uninhabited _, Shape.Bottom _, Shape.Erroneous _, Shape.Undecided _ ->
                    new Writing.NotWritable<>("nothing writes a value at a position of this type");
        };
    }

    /**
     * A primitive, written as what the position declares and holding what the value holds.
     *
     * <p>The value has to be of the primitive the position declares, as the value says
     * ({@link ObservedValue#primitive}): a date read where a time stands is not written as a time.
     * The one exception is the one a boundary makes: it carries a whole number where a
     * {@code Decimal} stands, so a value read as an integer at a decimal is a decimal.
     */
    private static Writing<FixtureTemplate> scalar(ObservedValue value, Type.Prim prim) {
        if (value.primitive() != prim
                && !(prim == Type.Prim.DECIMAL && value instanceof ObservedValue.Integer)) {
            return new Writing.NotWritable<>("the value is not one a " + prim + " is written as");
        }
        FixtureTemplate written = switch (prim) {
            case INT -> value instanceof ObservedValue.Integer(long n)
                    ? FixtureTemplate.integer(n) : null;
            case DECIMAL -> switch (value) {
                case ObservedValue.Decimal(BigDecimal d) -> FixtureTemplate.decimal(d);
                case ObservedValue.Integer(long n) -> FixtureTemplate.decimal(BigDecimal.valueOf(n));
                default -> null;
            };
            case STRING -> value instanceof ObservedValue.Text(String s)
                    ? FixtureTemplate.string(s) : null;
            case BOOL -> value instanceof ObservedValue.Bool(boolean b)
                    ? FixtureTemplate.bool(b) : null;
            case DATE -> value instanceof ObservedValue.Temporal(String iso)
                    ? FixtureTemplate.date(iso) : null;
            case TIME -> value instanceof ObservedValue.Temporal(String iso)
                    ? FixtureTemplate.time(iso) : null;
            case DATETIME -> value instanceof ObservedValue.Temporal(String iso)
                    ? FixtureTemplate.dateTime(iso) : null;
            case INSTANT -> value instanceof ObservedValue.Temporal(String iso)
                    ? FixtureTemplate.instant(iso) : null;
            // No row writes one: nothing composes a value of it anywhere.
            case RATIONAL -> null;
        };
        if (written != null) {
            return new Writing.Written<>(written);
        }
        // A decimal is the one primitive whose value can be in hand and still have no literal.
        return new Writing.NotWritable<>(
                prim == Type.Prim.DECIMAL && value instanceof ObservedValue.Decimal
                        ? "a decimal this far from an ordinary one has no literal"
                        : "the value is not one a " + prim + " is written as");
    }

    private static Writing<FixtureTemplate> unitCase(TypeSymbol made, RuleReadingContext reading) {
        return reading.source().symbols().scope().reach(made)
                instanceof TypeReachName.Written name
                ? new Writing.Written<>(FixtureTemplate.unitCase(name))
                : new Writing.NotWritable<>(WornNames.noSpellingFor(made));
    }

    /** A record, field by field in the order its declaration writes them. */
    private static Writing<FixtureTemplate> record(ObservedValue.Constructed made,
                                                   Shape.Product product,
                                                   RuleReadingContext reading) {
        if (!(reading.source().symbols().scope().reach(made.type())
                instanceof TypeReachName.Written name)) {
            return new Writing.NotWritable<>(WornNames.noSpellingFor(made.type()));
        }
        // The fields the declaration writes and no others: a field the value holds and the
        // declaration does not is a value of something else, and writing the declaration's would
        // drop it without a word.
        if (!made.fields().keySet().equals(product.fields().keySet())) {
            return notOf();
        }
        SequencedMap<String, FixtureTemplate> fields = new LinkedHashMap<>();
        for (Map.Entry<String, Type> field : product.fields().entrySet()) {
            ObservedValue held = made.field(field.getKey());
            if (held == null) {
                return new Writing.NotWritable<>(
                        "the value built holds nothing at `" + field.getKey() + "`");
            }
            switch (of(held, field.getValue(), reading)) {
                case Writing.Written<FixtureTemplate>(FixtureTemplate written) ->
                        fields.put(field.getKey(), written);
                case Writing.NotWritable<FixtureTemplate> no -> {
                    return no;
                }
            }
        }
        return new Writing.Written<>(FixtureTemplate.record(name, fields));
    }

    /** A list in the order it holds its elements, and a set in the order of their text. */
    private static Writing<FixtureTemplate> sequence(List<ObservedValue> elements,
                                                     Shape.Sequence sequence,
                                                     RuleReadingContext reading) {
        List<FixtureTemplate> written = new ArrayList<>();
        for (ObservedValue each : elements) {
            switch (of(each, sequence.element(), reading)) {
                case Writing.Written<FixtureTemplate>(FixtureTemplate one) -> written.add(one);
                case Writing.NotWritable<FixtureTemplate> no -> {
                    return no;
                }
            }
        }
        if (sequence.kind() == Shape.Sequence.Kind.SET) {
            written.sort(Comparator.comparing(FixtureTemplate::text));
        }
        return new Writing.Written<>(FixtureTemplate.collection(written));
    }

    /** A map as its entries, in the order of their text. */
    private static Writing<FixtureTemplate> mapping(List<ObservedValue.Entry> entries,
                                                    Shape.Mapping mapping,
                                                    RuleReadingContext reading) {
        List<FixtureTemplate> written = new ArrayList<>();
        for (ObservedValue.Entry each : entries) {
            Writing<FixtureTemplate> key = of(each.key(), mapping.key(), reading);
            if (!(key instanceof Writing.Written<FixtureTemplate>(FixtureTemplate k))) {
                return key;
            }
            Writing<FixtureTemplate> value = of(each.value(), mapping.value(), reading);
            if (!(value instanceof Writing.Written<FixtureTemplate>(FixtureTemplate v))) {
                return value;
            }
            written.add(FixtureTemplate.entry(k, v));
        }
        written.sort(Comparator.comparing(FixtureTemplate::text));
        return new Writing.Written<>(FixtureTemplate.collection(written));
    }

    private static <T> Writing<T> unread(ObservedValue value) {
        return new Writing.NotWritable<>(switch (value) {
            case ObservedValue.Unknown(String reason) -> "the value could not be read back: "
                    + reason;
            default -> "a limit stopped the observation before it reached the value";
        });
    }

    private static <T> Writing<T> notOf() {
        return new Writing.NotWritable<>(
                "the value built is not the construction the position declares");
    }

    private ObservedFixtures() {}
}
