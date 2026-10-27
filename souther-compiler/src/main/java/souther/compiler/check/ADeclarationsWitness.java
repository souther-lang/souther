package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * A value of a declaration, written down, that every rule of the declaration holds of.
 *
 * <p>That a declaration has a value is shown by exhibiting one. The rules are folded over the value
 * by the fold the discharge of a construction folds with ({@link CoreConstantEval}), so a rule that
 * comes out true here is true by the account of the operators that every other reader of a rule
 * has, and not by one of this class's own. A rule the fold cannot work out is a rule nothing is
 * shown of, and the declaration is then not shown to hold a value — which says nothing about
 * whether it does.
 *
 * <p>The value is made of the smallest values the rules mention. A number is tried at nought, at
 * one, and at each number a rule names and the numbers beside it, which is where an end of a range
 * lies and where a relation between two numbers is most likely to hold; a string at the empty one,
 * at two short ones and at those a rule names. The values of the places a value is made of are tried
 * in the order of how far each is from its first, so a value found is one of the least that the
 * values tried could be, and what is tried is bounded by {@link #MOST_TRIED} whatever the rules say.
 *
 * <p>What is found is a value of the declaration in full and what is not found is nothing more
 * than that. {@link #MOST_TRIED}, {@link #MOST_UNFOLDED} and {@link #MOST_DEEP} bound the search
 * and are no part of what a declaration means: a rule that folded to nothing at the values tried,
 * a search that reached its bound and values of which none held every rule all leave the
 * declaration not shown, and none of them says that no value exists.
 *
 * <p>A place holding something this does not write down — a sum, a date, a container with elements
 * a rule reads — is a place no value is written for, and the declaration then is not shown to hold
 * one. An optional is written as none and a list as an empty one, which the rules of the places
 * inside them do not reach.
 *
 * <p>Handed the rules in the form the reading of the declaration holds them in: each is over the
 * bindings of the declaration's own fields, and a rule of a declaration a field is of is written
 * over the field it is a rule of, so one fold over all of them is a check of the value in full.
 */
final class ADeclarationsWitness {

    /** How many values are tried before this gives up, which is what bounds the work a
     *  declaration with a rule it cannot satisfy by its first values costs. */
    static final int MOST_TRIED = 2048;

    /** How many declarations deep a value is written, which bounds a declaration holding itself. */
    private static final int MOST_DEEP = 6;

    /** How many values a rule is tried at without folding to anything before it is given up on. */
    private static final int MOST_UNFOLDED = 16;

    /** Where the values written down are said to stand: at the first rule, which is the code they are
     *  written for. */
    private final SourcePos pos;

    private final RuleReadingSource source;
    private final List<Core> rules;
    private final Map<String, BindingId> bindings;
    private final List<Shape> fields;
    private final List<String> names;
    private final List<Slot> slots = new ArrayList<>();

    private final Hints hints;

    private ADeclarationsWitness(RuleReadingSource source, List<Core> rules,
                                 Map<String, BindingId> bindings, List<String> names,
                                 List<Shape> fields, Hints hints) {
        this.hints = hints;
        this.pos = rules.getFirst().pos();
        this.source = source;
        this.rules = rules;
        this.bindings = bindings;
        this.names = names;
        this.fields = fields;
    }

    /**
     * Whether a value of {@code declared} is shown to exist: one that every one of {@code rules}
     * folds to true over.
     *
     * @param rules every rule that holds of a value of {@code declared}, over the bindings of its
     *              fields
     */
    static boolean exists(RuleReadingSource source, TypeSymbol.AtModule declared,
                          List<Core> rules, Hints hints) {
        Map<String, BindingId> bindings = source.bindings().of(declared);
        List<String> names = source.layout().of(declared);
        Map<String, Type> types = source.fieldTypes().of(declared);
        if (rules.isEmpty() || names.isEmpty() || !bindings.keySet().containsAll(names)) {
            return false;
        }
        List<Shape> fields = new ArrayList<>();
        Set<TypeSymbol.AtModule> within = new LinkedHashSet<>();
        within.add(declared);
        for (String name : names) {
            Shape shape = shapeOf(source, types.get(name), within, 1, List.of(name));
            if (shape == null) {
                return false;
            }
            fields.add(shape);
        }
        ADeclarationsWitness search = new ADeclarationsWitness(source, rules, bindings, names,
                fields, hints);
        return search.found();
    }

    /**
     * Strings the reading of a declaration says a place of it admits, which are where a string
     * rule is held: a pattern is a language, and no short string is likely to be in it.
     *
     * <p>Only proposals. What the reading admits is an upper bound, and a string is a value of the
     * declaration only when every rule folds to true over it, which is asked of each as of any
     * other.
     */
    interface Hints {

        /** Nothing proposed anywhere. */
        Hints NONE = _ -> List.of();

        /** Strings that may be the value at the place the fields {@code steps} reach, best first. */
        List<String> stringsAt(List<String> steps);
    }

    /** What a place of a value is written as. */
    private sealed interface Shape {}

    /** A place written with one of the values tried at it, which the reading of the declaration
     *  knows by the fields {@code place} reaches it through. */
    private record Slot(int at, Type.Prim type, List<String> place) implements Shape {}

    /** A place written as the value of a declaration made of places. */
    private record Product(TypeSymbol.AtModule declared, List<String> names, List<Shape> fields)
            implements Shape {}

    /** A place written as none, or as an empty list, which the rules of the places inside it do
     *  not reach. */
    private record Written(Type type) implements Shape {}

    /** The shape of a place of type {@code type}, or null where no value is written for it. */
    private static Shape shapeOf(RuleReadingSource source, Type type,
                                 Set<TypeSymbol.AtModule> within, int deep, List<String> at) {
        return switch (type) {
            case null -> null;
            case Type.Prim primitive -> switch (primitive) {
                case INT, DECIMAL, STRING, BOOL -> new Slot(-1, primitive, at);
                case RATIONAL, DATE, TIME, DATETIME, INSTANT -> null;
            };
            case Type.OptionOf option -> new Written(option);
            case Type.ListOf list -> new Written(list);
            case Type.Ref ref when ref.name() instanceof TypeSymbol.AtModule declared ->
                    productOf(source, declared, within, deep, at);
            default -> null;
        };
    }

    private static Shape productOf(RuleReadingSource source, TypeSymbol.AtModule declared,
                                   Set<TypeSymbol.AtModule> within, int deep, List<String> at) {
        if (deep > MOST_DEEP || within.contains(declared)
                || source.kinds().of(declared.key()) != DeclarationKind.PRODUCT) {
            return null;
        }
        List<String> names = source.layout().of(declared);
        Map<String, Type> types = source.fieldTypes().of(declared);
        if (names.isEmpty() || !types.keySet().containsAll(names)) {
            return null;
        }
        Set<TypeSymbol.AtModule> deeper = new LinkedHashSet<>(within);
        deeper.add(declared);
        List<Shape> fields = new ArrayList<>();
        for (String name : names) {
            // A newtype's value is the value that wears the name, so it is at the place the
            // newtype is; any other declaration's field is a step further in.
            List<String> inside = source.newtypes().of(declared.key()) ? at : deeperBy(at, name);
            Shape shape = shapeOf(source, types.get(name), deeper, deep + 1, inside);
            if (shape == null) {
                return null;
            }
            fields.add(shape);
        }
        return new Product(declared, names, fields);
    }

    private static List<String> deeperBy(List<String> at, String field) {
        List<String> out = new ArrayList<>(at);
        out.add(field);
        return List.copyOf(out);
    }

    /** Whether some value tried is one every rule holds of. */
    private boolean found() {
        List<Shape> numbered = new ArrayList<>();
        for (Shape each : fields) {
            numbered.add(numbered(each));
        }
        Pools pools = Pools.of(rules, pos);
        List<List<Core>> candidates = new ArrayList<>();
        for (Slot slot : slots) {
            List<Core> tried = new ArrayList<>();
            if (slot.type() == Type.Prim.STRING) {
                hints.stringsAt(slot.place()).forEach(
                        text -> tried.add(new Core.Str(text, Type.STRING, pos)));
            }
            tried.addAll(pools.of(slot.type()));
            candidates.add(tried);
        }
        int[] unfolded = new int[rules.size()];
        int[] tried = {0};
        int most = 0;
        for (List<Core> each : candidates) {
            most += each.size() - 1;
        }
        for (int rank = 0; rank <= most && tried[0] < MOST_TRIED; rank++) {
            int[] chosen = new int[slots.size()];
            if (tryAll(numbered, candidates, chosen, 0, rank, unfolded, tried)) {
                return true;
            }
            if (someRuleGivenUp(unfolded)) {
                return false;
            }
        }
        return false;
    }

    /** The shape with its slots numbered in the order they are met, each remembered. */
    private Shape numbered(Shape shape) {
        return switch (shape) {
            case Slot slot -> {
                Slot made = new Slot(slots.size(), slot.type(), slot.place());
                slots.add(made);
                yield made;
            }
            case Product product -> {
                List<Shape> inside = new ArrayList<>();
                for (Shape each : product.fields()) {
                    inside.add(numbered(each));
                }
                yield new Product(product.declared(), product.names(), inside);
            }
            case Written written -> written;
        };
    }

    /** Whether some choice of one candidate for each slot from {@code at} on, whose positions
     *  sum to {@code left}, is a value every rule holds of. */
    private boolean tryAll(List<Shape> numbered, List<List<Core>> candidates, int[] chosen,
                           int at, int left, int[] unfolded, int[] tried) {
        if (tried[0] >= MOST_TRIED) {
            return false;
        }
        if (at == chosen.length) {
            if (left != 0) {
                return false;
            }
            tried[0]++;
            return holds(numbered, candidates, chosen, unfolded);
        }
        int most = candidates.get(at).size() - 1;
        for (int index = 0; index <= Math.min(left, most); index++) {
            chosen[at] = index;
            if (tryAll(numbered, candidates, chosen, at + 1, left - index, unfolded, tried)) {
                return true;
            }
        }
        return false;
    }

    /** Whether every rule folds to true over the value made of {@code chosen}. */
    private boolean holds(List<Shape> numbered, List<List<Core>> candidates, int[] chosen,
                          int[] unfolded) {
        Map<BindingId, Core> given = new LinkedHashMap<>();
        for (int i = 0; i < names.size(); i++) {
            given.put(bindings.get(names.get(i)), valueOf(numbered.get(i), candidates, chosen));
        }
        CoreConstantEval fold = CoreConstantEval.against(source.symbols(), Denotations.none());
        boolean all = true;
        for (int i = 0; i < rules.size(); i++) {
            Optional<Object> folded = fold.eval(Clauses.substituted(rules.get(i), given));
            if (!(folded.orElse(null) instanceof Boolean answer)) {
                unfolded[i]++;
                all = false;
            } else if (!answer) {
                all = false;
            }
        }
        return all;
    }

    /** Whether some rule has been tried at enough values and folded to nothing at each: what it
     *  says is no constant over the values written, and more of them would not change that. */
    private boolean someRuleGivenUp(int[] unfolded) {
        for (int each : unfolded) {
            if (each >= MOST_UNFOLDED) {
                return true;
            }
        }
        return false;
    }

    private Core valueOf(Shape shape, List<List<Core>> candidates, int[] chosen) {
        return switch (shape) {
            case Slot slot -> candidates.get(slot.at()).get(chosen[slot.at()]);
            case Written written -> written.type() instanceof Type.OptionOf
                    ? new Core.OptionNone(written.type(), pos)
                    : new Core.ListLit(List.of(), written.type(), pos);
            case Product product -> {
                List<Core.FieldValue> values = new ArrayList<>();
                for (int i = 0; i < product.names().size(); i++) {
                    values.add(new Core.FieldValue(product.names().get(i),
                            valueOf(product.fields().get(i), candidates, chosen), pos));
                }
                yield new Core.Construct(product.declared(), values,
                        new Type.Ref(product.declared()), pos);
            }
        };
    }

    /**
     * The values tried at a place of each primitive type, in the order they are tried.
     *
     * <p>The values every type is tried at first, then each a rule writes and the ones beside it:
     * the whole numbers either side of a number, the decimals a step of the number's own scale
     * either side of a decimal.
     */
    private static final class Pools {

        private final List<Core> ints = new ArrayList<>();
        private final List<Core> decimals = new ArrayList<>();
        private final List<Core> strings = new ArrayList<>();
        private final List<Core> bools = new ArrayList<>();

        private Pools() {}

        static Pools of(List<Core> rules, SourcePos pos) {
            Pools out = new Pools();
            List<Long> longs = new ArrayList<>(List.of(0L, 1L, -1L));
            List<BigDecimal> decimals = new ArrayList<>(
                    List.of(BigDecimal.valueOf(0, 1), BigDecimal.valueOf(10, 1)));
            List<String> strings = new ArrayList<>(List.of("", "a", "0"));
            rules.forEach(rule -> out.mention(rule, longs, decimals, strings));
            for (long each : new LinkedHashSet<>(longs)) {
                out.ints.add(new Core.Int(each, Type.INT, pos));
            }
            for (BigDecimal each : new LinkedHashSet<>(decimals)) {
                out.decimals.add(new Core.Decimal(each, Type.DECIMAL, pos));
            }
            for (String each : new LinkedHashSet<>(strings)) {
                out.strings.add(new Core.Str(each, Type.STRING, pos));
            }
            out.bools.add(new Core.Bool(false, Type.BOOL, pos));
            out.bools.add(new Core.Bool(true, Type.BOOL, pos));
            return out;
        }

        /** The values {@code e} writes, and those beside them. */
        private void mention(Core e, List<Long> longs, List<BigDecimal> decimals,
                             List<String> strings) {
            switch (Core.withoutStanding(e)) {
                case Core.Int number -> {
                    longs.add(number.value());
                    longs.add(number.value() + 1);
                    longs.add(number.value() - 1);
                }
                case Core.Decimal number -> {
                    // The decimals one step of the number's own last place either side of it.
                    BigDecimal written = number.value();
                    decimals.add(written);
                    decimals.add(new BigDecimal(written.unscaledValue().add(BigInteger.ONE),
                            written.scale()));
                    decimals.add(new BigDecimal(written.unscaledValue().subtract(BigInteger.ONE),
                            written.scale()));
                }
                case Core.Str text -> strings.add(text.value());
                default -> { }
            }
            Core.forEachChild(Core.withoutStanding(e),
                    child -> mention(child, longs, decimals, strings));
        }

        List<Core> of(Type.Prim type) {
            return switch (type) {
                case INT -> ints;
                case DECIMAL -> decimals;
                case STRING -> strings;
                case BOOL -> bools;
                case RATIONAL, DATE, TIME, DATETIME, INSTANT -> List.of();
            };
        }
    }
}
