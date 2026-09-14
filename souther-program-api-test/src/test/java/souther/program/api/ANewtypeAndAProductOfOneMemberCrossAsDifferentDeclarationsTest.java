package souther.program.api;

import souther.compiler.core.ValueShape;
import souther.compiler.program.CheckedData;
import souther.compiler.program.CheckedModule;
import souther.compiler.program.CheckedProgram;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A data declared over another and a product declared with one member called {@code value} are told
 * apart by a reader of a checked program.
 *
 * <p>The two are made of the same thing: one field, of the same type, holding the same clauses. They
 * are written differently — {@code data X = Y} crosses as {@code Y} crosses and the braced one
 * crosses as an object — and the language says which by the syntax the declaration was written in
 * rather than by the shape it came out as (spec §newtype). So a reader handed the shape has nothing
 * to tell them by, and writing either as the other is silent: a build that reads the program and
 * writes the value agrees with itself either way, and what a document from one side means to the
 * other is where it shows.
 *
 * <p>Both directions, because either alone is kept by a reader that answers one way for everything.
 * And over a primitive and over a named data, because a derived codec writes a newtype over a
 * primitive as a bare scalar and one over anything else as that thing writes itself — two branches
 * of one rule, which a reader derives from the one fact this holds it is given.
 */
class ANewtypeAndAProductOfOneMemberCrossAsDifferentDeclarationsTest {

    /** Two pairs, each written the two ways: over a primitive and over a data of the module. */
    private static final String MODULE = """
            module demo

            data Inner = { n: Int }

            data OverText  = String
                invariant said = String.length(value) > 0

            data HoldsText = { value: String }
                invariant said = String.length(value) > 0

            data OverInner  = Inner
            data HoldsInner = { value: Inner }
            """;

    private static CheckedModule demo() {
        CheckedModule module = CheckedProgram.of(List.of(MODULE)).module("demo");
        assertNotNull(module, "the compile checked this module");
        return module;
    }

    private static CheckedData declared(CheckedModule module, String name) {
        for (CheckedData each : module.data()) {
            if (each.name().name().equals(name)) {
                return each;
            }
        }
        throw new AssertionError(name + " is not among this module's data");
    }

    private static List<String> fieldNames(CheckedData.WithFields built) {
        return built.fields().stream().map(ValueShape.Field::name).toList();
    }

    private static List<Type> fieldTypes(CheckedData.WithFields built) {
        return built.fields().stream().map(ValueShape.Field::type).toList();
    }

    /** What is declared over another is a {@link CheckedData.Newtype}, and says what it is over. */
    @Test
    void aDataDeclaredOverAnotherIsANewtypeOverThatType() {
        CheckedModule demo = demo();

        assertEquals(Type.STRING,
                assertInstanceOf(CheckedData.Newtype.class, declared(demo, "OverText")).wrapped());
        assertEquals(Type.ref(declared(demo, "Inner").name()),
                assertInstanceOf(CheckedData.Newtype.class, declared(demo, "OverInner")).wrapped());
    }

    /** And a product declared with one member is a {@link CheckedData.Product}, whatever the member
     *  is called. */
    @Test
    void aProductOfOneMemberCalledValueIsAProduct() {
        CheckedModule demo = demo();

        assertInstanceOf(CheckedData.Product.class, declared(demo, "HoldsText"));
        assertInstanceOf(CheckedData.Product.class, declared(demo, "HoldsInner"));
    }

    /**
     * And what they are made of does not separate them.
     *
     * <p>The half that says why the arm is the answer. A reader told to look at the fields is told
     * the same thing about both, member for member and type for type, so an answer worked out from
     * the shape — or from the name of the member, which is the same shape read one field in — is an
     * answer about neither.
     */
    @Test
    void andWhatTheyAreMadeOfIsTheSame() {
        CheckedModule demo = demo();

        for (List<String> pair : List.of(List.of("OverText", "HoldsText"),
                List.of("OverInner", "HoldsInner"))) {
            CheckedData.WithFields over = assertInstanceOf(CheckedData.WithFields.class,
                    declared(demo, pair.get(0)));
            CheckedData.WithFields holds = assertInstanceOf(CheckedData.WithFields.class,
                    declared(demo, pair.get(1)));

            assertEquals(fieldNames(holds), fieldNames(over), () -> "the members of " + pair);
            assertEquals(fieldTypes(holds), fieldTypes(over), () -> "what stands in them: " + pair);
            assertEquals(clauseNames(holds), clauseNames(over),
                    () -> "what must hold of one: " + pair);
        }

        assertEquals(List.of("said"),
                clauseNames(assertInstanceOf(CheckedData.WithFields.class,
                        declared(demo, "OverText"))),
                "one pair states a clause, so the comparison above is over something");
    }

    private static List<String> clauseNames(CheckedData.WithFields built) {
        return built.invariants().stream().map(each -> each.name().orElse("")).toList();
    }
}
