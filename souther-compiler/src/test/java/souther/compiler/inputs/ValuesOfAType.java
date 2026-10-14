package souther.compiler.inputs;

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
 * restated. Each value of each component is put with the first values of the others that the
 * constructor accepts, so where a constructor ties two components together the value made is one it
 * would make. And then it is checked that each component did come out varied alone, because a
 * constructor can refuse every value a component was offered but one.
 *
 * <p>Never null. Which component may be absent is said by a record's documentation and not by its
 * type, and several constructors here take a null nothing ever hands them; offered one, they make
 * values no order is owed for. An absence a record does mean is a pair written out by hand.
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
                    .toList());

    /**
     * The words a string component is offered.
     *
     * <p>The empty one among them because an absence is not a word that happens to be empty, and an
     * optional word is offered both.
     */
    private static final List<Object> WORDS = List.of("a", "b", "");

    private final Map<Type, List<Object>> made = new HashMap<>();

    private final Set<Type> making = new HashSet<>();

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
            offered.add(of(resolved(component.getGenericType(), bound)));
        }
        if (components.length == 0) {
            return List.of(made(canonical, new Object[0]).orElseThrow(() -> new AssertionError(
                    record.getName() + " holds nothing and refused to be made")));
        }
        Set<Object> out = new LinkedHashSet<>();
        for (int i = 0; i < components.length; i++) {
            for (Object value : offered.get(i)) {
                firstMadeWith(canonical, offered, i, value).ifPresent(out::add);
            }
        }
        List<Object> values = List.copyOf(out);
        for (int i = 0; i < components.length; i++) {
            if (!variedAlone(values, components, i)) {
                throw new AssertionError("no two values of " + record.getName() + " made here"
                        + " differ in " + components[i].getName() + " alone, so nothing asked"
                        + " over them says whether an order reads it");
            }
        }
        return values;
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
     * {@code value} at component {@code at}, beside the first values of the others the constructor
     * accepts, counting through them the way an odometer does.
     */
    private static Optional<Object> firstMadeWith(Constructor<?> canonical,
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
