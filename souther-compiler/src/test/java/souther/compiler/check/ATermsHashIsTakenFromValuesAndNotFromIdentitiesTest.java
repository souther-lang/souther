package souther.compiler.check;

import org.junit.jupiter.api.Test;

import java.lang.reflect.ParameterizedType;
import java.lang.reflect.RecordComponent;
import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Everything a term's hash is taken from is a value.
 *
 * <p>A term's hash has to be a function of the term. The interner files a term under it, {@link
 * Term#equals} reads it before anything else, and the cost of a chain of terms is what the table
 * holding them does with it — none of which is a statement about a term at all if the number moves
 * between runs of one program.
 *
 * <p>What can move it is an identity hash. {@code Enum.hashCode()} is {@code Object}'s, and on
 * HotSpot the default implementation draws from a sequence held per thread, so which number an enum
 * constant gets depends on when in that thread it was first hashed. Nothing about the program
 * decides that: under Surefire it is decided by which fork a class landed in and what ran before it.
 *
 * <p>So the walk here is over types and not over values. It starts at what the shapes say they carry
 * ({@link Term.Payload}), follows a record into its components and a sealed type into what it
 * permits, and asks at every node how {@link Term#ruleFor} takes a value of it. A node taken by its
 * own hash whose own hash is an identity is a finding, and the finding carries the path that reached
 * it — the type on its own says nothing about why a term's hash depends on it.
 *
 * <p>Following the components matters as much as following the payload. A record's generated hash
 * is its components' hashes, so a payload that is a record of a record of a sealed type of a record
 * of an enum is hashed by that enum's identity with no enum in sight.
 */
class ATermsHashIsTakenFromValuesAndNotFromIdentitiesTest {

    /** A class whose hash is a function of its value and is written in the platform. */
    private static final Set<Class<?>> SCALARS = Set.of(
            String.class, Long.class, Integer.class, Boolean.class, BigDecimal.class,
            int.class, long.class, boolean.class, char.class, double.class, float.class,
            short.class, byte.class);

    /** What reached a type, so that a finding names the payload it is under and not only itself. */
    private record Path(List<String> steps) {

        Path then(String step) {
            List<String> next = new ArrayList<>(steps);
            next.add(step);
            return new Path(next);
        }

        @Override
        public String toString() {
            return String.join("\n       → ", steps);
        }
    }

    private final List<String> findings = new ArrayList<>();
    private final Set<java.lang.reflect.Type> walked = new LinkedHashSet<>();

    @Test
    void nothingATermIsHashedFromIsHashedByItsIdentity() {
        walkType(Term.Shape.class, new Path(List.of("Term.hashOf(shape)")));
        for (Term.Shape shape : Term.Shape.values()) {
            walkPayload(shape.payload(), new Path(List.of("Shape." + shape + " carries")));
        }

        // The count says what was looked at. A walk that stopped early reports nothing and reads
        // exactly like one that reached everything.
        assertEquals(List.of(), findings, "a term's hash is taken from values, over the "
                + walked.size() + " types the payloads reach:\n\n"
                + String.join("\n\n", findings) + "\n");
    }

    private void walkPayload(Term.Payload payload, Path path) {
        switch (payload) {
            case Term.Payload.Nothing ignored -> { }
            case Term.Payload.OfType(Class<?> type) -> walkType(type, path.then(type.getSimpleName()));
            case Term.Payload.OfList(Term.Payload element) ->
                    walkPayload(element, path.then("each element"));
        }
    }

    private void walkType(java.lang.reflect.Type type, Path path) {
        if (!walked.add(type)) {
            return;
        }
        switch (type) {
            case ParameterizedType parameterized -> {
                for (java.lang.reflect.Type argument : parameterized.getActualTypeArguments()) {
                    walkType(argument, path.then("each " + shown(parameterized.getRawType())));
                }
            }
            case Class<?> raw -> walkClass(raw, path);
            default -> findings.add("no rule reaches " + shown(type) + ", under\n       " + path);
        }
    }

    private void walkClass(Class<?> type, Path path) {
        if (SCALARS.contains(type)) {
            return;
        }
        if (type.isInterface() || java.lang.reflect.Modifier.isAbstract(type.getModifiers())) {
            Class<?>[] permitted = type.getPermittedSubclasses();
            if (permitted == null || permitted.length == 0) {
                findings.add(shown(type) + " is open, so what a term is hashed from is not known,"
                        + " under\n       " + path);
                return;
            }
            for (Class<?> subtype : permitted) {
                walkType(subtype, path.then(shown(subtype)));
            }
            return;
        }
        switch (Term.ruleFor(type)) {
            case AN_ENUM_BY_NAME -> {
                if (!type.isEnum()) {
                    findings.add(shown(type) + " is taken as an enum and is none, under\n       "
                            + path);
                }
            }
            case ITS_OWN_HASH -> {
                // Taken at its word, and the word is what is checked: a type answering which two of
                // it are one by which object it is answers a different question every run.
                if (hashesByItsIdentity(type)) {
                    findings.add(shown(type) + " is taken by its own hash, and its own hash is its"
                            + " identity, under\n       " + path);
                }
            }
            case ITS_COMPONENTS -> {
                if (!type.isRecord()) {
                    findings.add(shown(type) + " is taken by its components and has none, under\n"
                            + "       " + path);
                } else {
                    walkComponents(type, path);
                }
            }
            case ITS_ELEMENTS -> findings.add(shown(type)
                    + " is taken by its elements, which a class does not say, under\n       " + path);
            case NONE_HERE -> findings.add("nothing takes " + shown(type) + ", under\n       " + path);
        }
    }

    private void walkComponents(Class<?> type, Path path) {
        for (RecordComponent component : type.getRecordComponents()) {
            walkType(component.getGenericType(), path.then(shown(type) + "." + component.getName()));
        }
    }

    /** Whether a value of {@code type} is hashed by which object it is rather than by what it is. */
    private static boolean hashesByItsIdentity(Class<?> type) {
        if (Enum.class.isAssignableFrom(type)) {
            return true;
        }
        try {
            return type.getMethod("hashCode").getDeclaringClass() == Object.class;
        } catch (NoSuchMethodException e) {
            return true;
        }
    }

    private static String shown(java.lang.reflect.Type type) {
        return type instanceof Class<?> c ? c.getSimpleName() : type.getTypeName();
    }
}
