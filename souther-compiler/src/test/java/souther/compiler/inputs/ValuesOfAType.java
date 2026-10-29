package souther.compiler.inputs;

import souther.compiler.numeric.ExactCut;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.RecordComponent;
import java.lang.reflect.Type;
import java.lang.reflect.TypeVariable;
import java.lang.reflect.WildcardType;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;

/**
 * Values of a type, made so that every component of every record the type reaches is varied on its
 * own.
 *
 * <p>What a law about an order is asked over. An order that leaves out a component calls two values
 * one exactly where they differ in that component and nothing else, so what has to be in hand is,
 * for each component, two values that differ there alone. Hand-written pairs say that for the
 * components somebody thought of, and a component added later is in none of them.
 *
 * <p><b>Read off the type, so a member or a component added later is made without anybody adding
 * it.</b> A sealed type is its permitted subclasses, a record its canonical constructor, an enum its
 * constants, a list or an optional what it can hold. Only a type that says none of those is written
 * here ({@link #LEAVES}), and a type that is neither read nor written is refused rather than passed
 * over: a value nobody can make is a component nothing would be asked about.
 *
 * <p>A record's constructor decides which combinations are values, and is asked rather than
 * restated. Each value of each component is put with values of the others the constructor accepts,
 * so where a constructor ties two components together the value made is one it would make.
 *
 * <p><b>Two things are asked of that, and only one of them is held over every combination.</b> That
 * each component comes out varied alone is what an order is held to, and it is asked over every
 * combination of the others wherever the nearer ones leave it unanswered: a component is refused
 * only where no combination varies it alone. That each value a component is offered comes out in
 * some value is not what an order is held to — an order over a component is asked over that
 * component's own values where its type is asked — so each is put beside the nearest values of the
 * others, the first of each with one or two of them moved, and a value the constructor takes only
 * beside more moved than that is not made. Asked over every combination, a value no combination takes —
 * a null where a component is never absent — asked one record the same question the better part of
 * a million times. What that leaves out is held against every combination, nightly
 * ({@link #everyCombination}, {@code TheNearestValuesOfATypeAreTheValuesEveryCombinationMakesTest}),
 * so a record that comes to take a value only far from the first ones is named there.
 *
 * <p>Null is offered for every component that is not a primitive, and the constructor says whether
 * it is a value. An absence a record means — the owner of a construct no source wrote — is one an
 * order is owed an answer for, and one it does not mean is refused where the record is made.
 *
 * <p>Not a proof about every value. An order that read a word by its length would pass every pair
 * here whose words differ in length; what this holds is that no component is left out.
 */
final class ValuesOfAType {

    /**
     * What a type that says nothing of its values is made from.
     *
     * <p>A declaration's identity is not a record, because its constructor would be as public as the
     * record; it is minted from a key and nowhere else, so it is made the way it is minted.
     */
    private static final Map<Class<?>, Function<ValuesOfAType, List<Object>>> LEAVES = Map.of(
            TypeSymbol.AtModule.class, values -> values.of(TypeKey.class).stream()
                    .<Object>map(key -> TypeSymbols.declared((TypeKey) key))
                    .toList(),
            WhatARelationLeavesUndivided.SettledRun.class, _ -> List.of(
                    new WhatARelationLeavesUndivided.SettledRun(null,
                            ExactCut.exclusive(ExactRatio.ZERO), false),
                    new WhatARelationLeavesUndivided.SettledRun(
                            ExactCut.exclusive(ExactRatio.ZERO), null, true),
                    new WhatARelationLeavesUndivided.SettledRun(
                            ExactCut.inclusive(ExactRatio.ZERO), ExactCut.inclusive(ExactRatio.ONE),
                            true),
                    new WhatARelationLeavesUndivided.SettledRun(null, null, false)));

    /**
     * The words a string component is offered.
     *
     * <p>The empty one among them because an absence is not a word that happens to be empty, and an
     * optional word is offered both.
     */
    private static final List<Object> WORDS = List.of("a", "b", "");

    private final Map<Type, List<Object>> made = new HashMap<>();

    private final Set<Type> making = new HashSet<>();

    /** Whether each value of each component is put beside every combination of the others, and
     *  not only the nearest ones. */
    private final boolean everyCombination;

    /** Values made with each value of a component beside the nearest values of the others. */
    ValuesOfAType() {
        this(false);
    }

    private ValuesOfAType(boolean everyCombination) {
        this.everyCombination = everyCombination;
    }

    /**
     * Values made with each value of each component beside every combination of the others: every
     * value the constructor takes anywhere, at what that costs. What the nearest values are held
     * against.
     */
    static ValuesOfAType everyCombination() {
        return new ValuesOfAType(true);
    }

    /**
     * Each value of a component of a record {@code every} has made that it made some value with and
     * {@code nearest} made none with, named by the record and the component — empty where the
     * nearest values leave out nothing every combination takes.
     *
     * <p>By the values of each component and not by the values made: the two put a value beside
     * different values of the others, and what the nearest ones are held to is that each value is
     * in some value made, not that it is beside the same ones.
     *
     * <p>Every record made, a generic one among them: what is a record is the type's question and
     * not how it was asked for, and a record over type arguments is made as that type, with the
     * values its arguments have.
     */
    static List<String> valuesLeftOut(ValuesOfAType nearest, ValuesOfAType every) {
        List<String> out = new ArrayList<>();
        for (Type type : List.copyOf(every.made.keySet())) {
            Class<?> record = switch (type) {
                case Class<?> c -> c;
                case ParameterizedType p when p.getRawType() instanceof Class<?> c -> c;
                default -> null;
            };
            if (record == null || !record.isRecord()) {
                continue;
            }
            for (RecordComponent component : record.getRecordComponents()) {
                Set<Optional<Object>> taken = valuesAt(every.of(type), component);
                taken.removeAll(valuesAt(nearest.of(type), component));
                if (!taken.isEmpty()) {
                    out.add(type.getTypeName() + "." + component.getName() + ": " + taken);
                }
            }
        }
        out.sort(null);
        return out;
    }

    private static Set<Optional<Object>> valuesAt(List<Object> values, RecordComponent component) {
        Set<Optional<Object>> out = new LinkedHashSet<>();
        for (Object value : values) {
            out.add(Optional.ofNullable(component(value, component)));
        }
        return out;
    }

    /** Values of {@code type}, every component of every record it reaches varied on its own. */
    List<Object> of(Type type) {
        List<Object> already = made.get(type);
        if (already != null) {
            return already;
        }
        if (!making.add(type)) {
            throw new AssertionError(type + " is reached from inside itself, and a value of it"
                    + " cannot be made by making its parts first");
        }
        List<Object> out = List.copyOf(ofUnmade(type));
        making.remove(type);
        made.put(type, out);
        return out;
    }

    private List<Object> ofUnmade(Type type) {
        return switch (type) {
            case Class<?> c -> ofAClass(c);
            case ParameterizedType p -> ofAParameterized(p);
            case WildcardType w -> of(w.getUpperBounds()[0]);
            default -> throw new AssertionError("no value of " + type + " can be made here");
        };
    }

    private List<Object> ofAClass(Class<?> c) {
        if (c == boolean.class || c == Boolean.class) {
            return List.of(false, true);
        }
        if (c == int.class || c == Integer.class) {
            return List.of(0, 1, -1);
        }
        if (c == long.class || c == Long.class) {
            return List.of(0L, 1L, -1L);
        }
        if (c == String.class) {
            return WORDS;
        }
        if (c.isEnum()) {
            return List.of(c.getEnumConstants());
        }
        Function<ValuesOfAType, List<Object>> leaf = LEAVES.get(c);
        if (leaf != null) {
            return leaf.apply(this);
        }
        if (c.isRecord()) {
            return ofARecord(c, Map.of());
        }
        if (c.isSealed()) {
            List<Object> out = new ArrayList<>();
            for (Class<?> member : c.getPermittedSubclasses()) {
                out.addAll(of(member));
            }
            return out;
        }
        throw new AssertionError("no value of " + c.getName() + " can be made here: it is not a"
                + " record, a sealed type or an enum, and nothing says how one is made");
    }

    private List<Object> ofAParameterized(ParameterizedType p) {
        Class<?> raw = (Class<?>) p.getRawType();
        Type[] arguments = p.getActualTypeArguments();
        if (raw == List.class) {
            List<Object> elements = of(arguments[0]);
            List<Object> out = new ArrayList<>();
            out.add(List.of());
            elements.forEach(each -> out.add(List.of(each)));
            if (elements.size() > 1) {
                out.add(List.of(elements.get(0), elements.get(1)));
            }
            return out;
        }
        if (raw == Optional.class) {
            List<Object> out = new ArrayList<>();
            out.add(Optional.empty());
            of(arguments[0]).forEach(each -> out.add(Optional.of(each)));
            return out;
        }
        if (raw.isRecord()) {
            Map<TypeVariable<?>, Type> bound = new HashMap<>();
            TypeVariable<?>[] parameters = raw.getTypeParameters();
            for (int i = 0; i < parameters.length; i++) {
                bound.put(parameters[i], arguments[i]);
            }
            return ofARecord(raw, bound);
        }
        throw new AssertionError("no value of " + p + " can be made here");
    }

    private List<Object> ofARecord(Class<?> record, Map<TypeVariable<?>, Type> bound) {
        RecordComponent[] components = record.getRecordComponents();
        Constructor<?> canonical = canonical(record, components);
        List<List<Object>> offered = new ArrayList<>();
        for (RecordComponent component : components) {
            List<Object> each = new ArrayList<>(of(resolved(component.getGenericType(), bound)));
            if (!component.getType().isPrimitive()) {
                each.add(null);
            }
            offered.add(each);
        }
        if (components.length == 0) {
            return List.of(made(canonical, new Object[0]).orElseThrow(() -> new AssertionError(
                    record.getName() + " holds nothing and refused to be made")));
        }
        Set<Object> out = new LinkedHashSet<>();
        for (int i = 0; i < components.length; i++) {
            for (Object value : offered.get(i)) {
                (everyCombination ? anyMadeWith(canonical, offered, i, value)
                        : nearestMadeWith(canonical, offered, i, value)).ifPresent(out::add);
            }
        }
        // A component the nearest values leave varied alone in no two of them is asked again over
        // every combination of the others, and refused only if that finds none either: that the
        // nearest ones held no such pair says where the asking stopped, not that there is none.
        for (int i = 0; i < components.length; i++) {
            if (variedAlone(List.copyOf(out), components, i)) {
                continue;
            }
            for (Object value : offered.get(i)) {
                anyMadeWith(canonical, offered, i, value).ifPresent(out::add);
            }
            if (!variedAlone(List.copyOf(out), components, i)) {
                throw new AssertionError("no two values of " + record.getName() + " differ in "
                        + components[i].getName() + " alone, whatever the other components are,"
                        + " so nothing asked over them says whether an order reads it");
            }
        }
        return List.copyOf(out);
    }

    private static Type resolved(Type type, Map<TypeVariable<?>, Type> bound) {
        if (type instanceof TypeVariable<?> variable) {
            Type to = bound.get(variable);
            return to != null ? to : variable.getBounds()[0];
        }
        return type;
    }

    private static Constructor<?> canonical(Class<?> record, RecordComponent[] components) {
        Class<?>[] types = Arrays.stream(components)
                .map(RecordComponent::getType)
                .toArray(Class<?>[]::new);
        try {
            Constructor<?> out = record.getDeclaredConstructor(types);
            out.setAccessible(true);
            return out;
        } catch (NoSuchMethodException e) {
            throw new AssertionError(record.getName() + " has no canonical constructor", e);
        }
    }

    /**
     * {@code value} at component {@code at}, beside the nearest values of the others the
     * constructor accepts: the first value of each, then each other component moved off its first
     * value alone, then each two of them moved together — or nothing where none of those is
     * accepted, which is where this stopped asking and not that no combination is.
     *
     * <p>Nearest first because what a constructor ties a value to is one or two other components —
     * an origin no source wrote is one with no ordinal and no owner — and a value it refuses
     * whatever stands beside it, a null where a component is never absent, is refused at every
     * combination: counting through all of them for each such value asked one record of four
     * components the same question the better part of a million times. Where the nearest values
     * leave a component varied alone in no two of them, {@link #ofARecord} asks that component again
     * over every combination ({@link #anyMadeWith}).
     */
    private static Optional<Object> nearestMadeWith(Constructor<?> canonical,
                                                    List<List<Object>> offered, int at,
                                                    Object value) {
        Object[] first = new Object[offered.size()];
        for (int i = 0; i < first.length; i++) {
            first[i] = i == at ? value : offered.get(i).get(0);
        }
        Optional<Object> made = made(canonical, first);
        for (int one = 0; one < first.length && made.isEmpty(); one++) {
            for (int a = 1; one != at && a < offered.get(one).size() && made.isEmpty(); a++) {
                Object[] moved = first.clone();
                moved[one] = offered.get(one).get(a);
                made = made(canonical, moved);
            }
        }
        for (int one = 0; one < first.length && made.isEmpty(); one++) {
            for (int other = one + 1; one != at && other < first.length && made.isEmpty();
                    other++) {
                for (int a = 1; other != at && a < offered.get(one).size() && made.isEmpty();
                        a++) {
                    for (int b = 1; b < offered.get(other).size() && made.isEmpty(); b++) {
                        Object[] moved = first.clone();
                        moved[one] = offered.get(one).get(a);
                        moved[other] = offered.get(other).get(b);
                        made = made(canonical, moved);
                    }
                }
            }
        }
        return made;
    }

    /**
     * {@code value} at component {@code at}, beside the first values of the others the constructor
     * accepts among every combination of them, counted through as an odometer does — or nothing
     * where it accepts none.
     */
    private static Optional<Object> anyMadeWith(Constructor<?> canonical,
                                                List<List<Object>> offered, int at, Object value) {
        int[] index = new int[offered.size()];
        while (true) {
            Object[] arguments = new Object[offered.size()];
            for (int i = 0; i < arguments.length; i++) {
                arguments[i] = i == at ? value : offered.get(i).get(index[i]);
            }
            Optional<Object> made = made(canonical, arguments);
            if (made.isPresent()) {
                return made;
            }
            int turning = offered.size() - 1;
            while (turning >= 0) {
                if (turning != at && ++index[turning] < offered.get(turning).size()) {
                    break;
                }
                index[turning] = 0;
                turning--;
            }
            if (turning < 0) {
                return Optional.empty();
            }
        }
    }

    /** What the constructor makes of {@code arguments}, or nothing where it refuses them. */
    private static Optional<Object> made(Constructor<?> canonical, Object[] arguments) {
        try {
            return Optional.of(canonical.newInstance(arguments));
        } catch (InvocationTargetException e) {
            if (e.getCause() instanceof IllegalArgumentException
                    || e.getCause() instanceof IllegalStateException
                    || e.getCause() instanceof NullPointerException) {
                return Optional.empty();
            }
            throw new AssertionError("making " + canonical.getDeclaringClass().getName()
                    + " out of " + Arrays.toString(arguments) + " failed", e.getCause());
        } catch (ReflectiveOperationException e) {
            throw new AssertionError(e);
        }
    }

    /** Whether two of {@code values} agree in every component but {@code at} and differ there. */
    private static boolean variedAlone(List<Object> values, RecordComponent[] components, int at) {
        Map<List<Object>, Set<Object>> byTheOthers = new HashMap<>();
        for (Object value : values) {
            List<Object> others = new ArrayList<>();
            for (int i = 0; i < components.length; i++) {
                if (i != at) {
                    others.add(component(value, components[i]));
                }
            }
            Set<Object> here = byTheOthers.computeIfAbsent(others, _ -> new HashSet<>());
            here.add(Optional.ofNullable(component(value, components[at])));
            if (here.size() > 1) {
                return true;
            }
        }
        return false;
    }

    private static Object component(Object value, RecordComponent component) {
        try {
            component.getAccessor().setAccessible(true);
            return component.getAccessor().invoke(value);
        } catch (ReflectiveOperationException e) {
            throw new AssertionError(e);
        }
    }
}
