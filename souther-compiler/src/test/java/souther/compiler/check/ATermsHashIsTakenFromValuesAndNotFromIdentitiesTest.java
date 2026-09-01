package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.ast.Hir;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.ValueName;

import java.lang.reflect.ParameterizedType;
import java.lang.reflect.RecordComponent;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
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

    private static final SourcePos POS = new SourcePos(1, 1);
    private static final Hir.Binders BINDERS =
            new Hir.Binders(new BindingOwner.OfValue("demo", "test"));

    /** What a component declared as a primitive arrives as, since a hash is taken of the value and a
     *  value handed over as an {@code Object} is the box. */
    private static final Map<Class<?>, Class<?>> BOXED = Map.of(
            int.class, Integer.class, long.class, Long.class, boolean.class, Boolean.class,
            char.class, Character.class, double.class, Double.class, float.class, Float.class,
            short.class, Short.class, byte.class, Byte.class);

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

    /**
     * What the shapes say they carry is what the interner builds them with.
     *
     * <p>The other test walks from what the shapes say. Said and built are two things, and a walk
     * over what was said proves what was said: writing {@code OP} down as carrying a string leaves
     * the whole suite green and takes {@code BinOp} out of the walk without a word. So the interner
     * is asked to build one term of every shape, and the check that a shape carries what it says it
     * carries is in the constructor, where every term goes through — under assertions, which is
     * every run of this suite.
     *
     * <p>Every shape and not the ones that came to mind: a shape nothing here builds is a shape the
     * constructor's check never sees, and the two tests together would then be proving something
     * about a smaller set than there is.
     */
    @Test
    void everyShapeIsBuiltWithWhatItSaysItCarries() {
        Term.Interner interned = new Term.Interner();
        BindingId x = BINDERS.binder("x", POS).id();
        TypeSymbol data = TypeSymbols.declared(new TypeKey("m", "D"));
        Term one = interned.written(1L);
        Term evaluated = interned.evaluated(new EvaluationId("an answer", POS, 0));

        Set<Term.Shape> built = new LinkedHashSet<>();
        for (Term term : List.of(
                interned.at(Location.of(x)),
                interned.bound(0, 0),
                interned.on(evaluated, List.of("a")),
                one,
                interned.written(java.math.BigDecimal.ONE),
                interned.written("s"),
                interned.written(true),
                interned.unit(data),
                interned.negated(one),
                interned.not(interned.written(true)),
                interned.comparison(
                        ((ComparisonClaim) ComparisonPlacement.of(BinOp.EQ)).canonical(one, one)),
                interned.operator(BinOp.ADD, one, one),
                interned.list(List.of(one)),
                interned.tuple(List.of(one)),
                interned.part(one, 0),
                interned.choice(one, one, one),
                interned.closure(1, one),
                interned.let(one, one),
                interned.built(data, List.of("f"), List.of(one)),
                interned.called(new ValueName.Helper("m", "f"), List.of(one)),
                evaluated,
                interned.some(one),
                interned.held(evaluated),
                interned.handed(one, 0),
                interned.none(Type.INT),
                interned.opened(one, Type.INT),
                interned.matched(one, List.of(List.of(data)), List.of(one)),
                interned.attempted(one, List.of("c"), List.of(one)))) {
            built.add(term.shape());
        }

        assertEquals(Set.of(Term.Shape.values()), built,
                "every shape is built here, so that what each carries is checked as it is built");
    }

    /**
     * Two sets holding the same things are one hash, whichever order they hand them over in.
     *
     * <p>What a set's equality reads is what it holds and not the order it walks it, so a hash
     * taken by folding the elements up in the order they arrive gives two equal values two hashes —
     * and a term carrying either is then two terms to the table and one term to the comparison.
     */
    @Test
    void twoSetsHoldingAlikeAreOneHashWhateverOrderTheyWalkIn() {
        TypeSymbol one = TypeSymbols.declared(new TypeKey("m", "A"));
        TypeSymbol other = TypeSymbols.declared(new TypeKey("m", "B"));
        Type forwards = new Type.Union(new LinkedHashSet<>(List.of(one, other)));
        Type backwards = new Type.Union(new LinkedHashSet<>(List.of(other, one)));

        assertEquals(forwards, backwards, "the two are one value");
        assertEquals(Term.hashOf(forwards), Term.hashOf(backwards), "so they are one hash");
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
            // The container is asked about before what it holds. A walk that went straight to the
            // arguments would prove the elements of a collection nothing says how to hash, which is
            // what a set of type symbols was: its elements were walked and the set itself fell
            // through to its own hash, which is the sum of theirs.
            case ParameterizedType parameterized -> {
                Class<?> raw = (Class<?>) parameterized.getRawType();
                Term.Rule holds = Term.ruleFor(raw);
                if (holds != Term.Rule.ITS_ELEMENTS && holds != Term.Rule.ITS_UNORDERED_ELEMENTS) {
                    findings.add(shown(raw) + " holds what a term is hashed from and nothing says"
                            + " how it is taken (" + holds + "), under\n       " + path);
                    return;
                }
                walkType(parameterized.getActualTypeArguments()[0],
                        path.then("each " + shown(raw)));
            }
            case Class<?> raw -> walkClass(raw, path);
            default -> findings.add("no rule reaches " + shown(type) + ", under\n       " + path);
        }
    }

    private void walkClass(Class<?> raw, Path path) {
        Class<?> type = BOXED.getOrDefault(raw, raw);
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
            case THE_PARTS_IT_NAMES -> {
                for (java.lang.reflect.Method part : Term.readersOf(type)) {
                    walkType(part.getGenericReturnType(),
                            path.then(shown(type) + " stands for its " + part.getName()));
                }
            }
            case ITS_ELEMENTS, ITS_UNORDERED_ELEMENTS -> findings.add(shown(type)
                    + " is taken by its elements, and what it holds is not written down here,"
                    + " under\n       " + path);
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
