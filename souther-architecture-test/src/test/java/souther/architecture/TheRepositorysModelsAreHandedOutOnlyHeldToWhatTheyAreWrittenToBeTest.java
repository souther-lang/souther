package souther.architecture;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Compilation;

import java.lang.classfile.Attributes;
import java.lang.classfile.ClassModel;
import java.lang.classfile.FieldModel;
import java.lang.classfile.MethodModel;
import java.lang.reflect.AccessFlag;
import java.util.List;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The repository's models are handed out only as what they are written to be.
 *
 * <p>A corpus is written to compile or to be refused with the errors it declares, and a test that
 * takes the compilation and holds it to one of those by its own choosing holds some of them to the
 * wrong one. So {@code RepositoryModels} gives no compilation at all: it gives a {@code Model},
 * and the one way from that to the compilation is {@code answered()}, which holds it to what the
 * corpus declares. There is nothing a test can choose, and so nothing to find in the tests.
 *
 * <p>This holds the shape of that API and not what a test does with a compilation it already holds.
 * A member added to {@code RepositoryModels}, {@code Model}, {@code ConformanceCorpus} or its
 * analysis that gives a compilation, or a collection of them, as it is, is the way back to the
 * choice. What a test writes beside one is not looked for: that a corpus's refusals are not said
 * a second time is a property of the tests, and a spelling in them is not that property.
 */
class TheRepositorysModelsAreHandedOutOnlyHeldToWhatTheyAreWrittenToBeTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofEverythingCompiledHere();

    private static final String POPULATION = "souther/compiler/conformance/RepositoryModels";

    private static final String COMPILATION = "Lsouther/compiler/query/Compilation;";

    @Test
    void thePopulationHandsOutNoCompilation() {
        assertEquals(List.of(), handingOutACompilation(COMPILED.read(POPULATION)),
                "RepositoryModels hands out a compilation as it is, which a test may then hold to"
                        + " what it chooses: hand out a Model");
    }

    @Test
    void aModelHandsOutItsCompilationOnlyHeldToWhatItIsWrittenToBe() {
        assertEquals(List.of("answered"),
                handingOutACompilation(COMPILED.read(POPULATION + "$Model")),
                "a Model gives a compilation by a way other than answered()");
    }

    /**
     * And so does a corpus and its analysis, which are the other ways to a model of the
     * repository: what they hand out is the compilation held to what the corpus is written to be,
     * and no compilation as it is.
     */
    @Test
    void aCorpusAndItsAnalysisHandOutTheirCompilationOnlyHeldToWhatItIsWrittenToBe() {
        assertEquals(List.of("answered"),
                handingOutACompilation(COMPILED.read("souther/compiler/conformance/ConformanceCorpus")),
                "a corpus gives a compilation by a way other than answered()");
        assertEquals(List.of("answered"),
                handingOutACompilation(
                        COMPILED.read("souther/compiler/conformance/ConformanceCorpus$Analysed")),
                "an analysis gives a compilation by a way other than answered()");
    }

    /**
     * And the check sees what it is about: the helper hands a compilation out, and a method that
     * hands out a collection of them is seen through its generic signature, which the descriptor
     * does not carry.
     */
    @Test
    void andTheCheckSeesACompilationHandedOutAsItIsOrInACollection() {
        assertFalse(handingOutACompilation(COMPILED.read("souther/compiler/ACompiledModel")).isEmpty(),
                "ACompiledModel hands compilations out, so a check that finds none reads nothing");
        assertEquals(List.of("HELD", "array", "collected", "samePackage", "single"),
                handingOutACompilation(COMPILED.read(Sample.class.getName().replace('.', '/'))));
    }

    /** What a check of this shape has to find. */
    static final class Sample {

        public static final List<Compilation> HELD = List.of();

        private Sample() { }

        public static List<Compilation> collected() {
            return List.of();
        }

        public static Compilation single() {
            return null;
        }

        public static Compilation[] array() {
            return new Compilation[0];
        }

        /** Not public, and a test in the package of the class it is in reaches it all the same. */
        static Compilation samePackage() {
            return null;
        }
    }

    /**
     * And a type is told by the whole of its name, which ends where the descriptor says it does: an
     * array of compilations holds one, and a type whose name only begins like it does not.
     */
    @Test
    void andATypeIsToldByTheWholeOfItsName() {
        assertTrue(mentionsACompilation("[Lsouther/compiler/query/Compilation;"));
        assertTrue(mentionsACompilation("Ljava/util/Map<Ljava/lang/String;"
                + "Lsouther/compiler/query/Compilation;>;"));
        assertFalse(mentionsACompilation("Ljava/util/List<Lsouther/compiler/query/CompilationDetails;>;"));
        assertFalse(mentionsACompilation("Lsouther/compiler/query/Compilations;"));
    }

    /** Whether a descriptor, or a generic signature, names the compilation type anywhere in it. */
    private static boolean mentionsACompilation(String typeText) {
        return typeText.contains(COMPILATION);
    }

    /**
     * The methods of the class that return a compilation, or a type holding one, and the fields
     * that hold one, by name, whatever their access but private.
     *
     * <p>Not only the public ones: a test beside the class reaches what is package-private, and
     * the test that failed on the corpora is beside the class that held them.
     */
    private static List<String> handingOutACompilation(ClassModel model) {
        TreeSet<String> found = new TreeSet<>();
        for (MethodModel method : model.methods()) {
            if (method.flags().has(AccessFlag.PRIVATE)) {
                continue;
            }
            String descriptor = method.methodTypeSymbol().returnType().descriptorString();
            String generic = method.findAttribute(Attributes.signature())
                    .map(signature -> signature.signature().stringValue())
                    .map(whole -> whole.substring(whole.lastIndexOf(')') + 1))
                    .orElse("");
            if (mentionsACompilation(descriptor) || mentionsACompilation(generic)) {
                found.add(method.methodName().stringValue());
            }
        }
        for (FieldModel field : model.fields()) {
            if (field.flags().has(AccessFlag.PRIVATE)) {
                continue;
            }
            String generic = field.findAttribute(Attributes.signature())
                    .map(signature -> signature.signature().stringValue())
                    .orElse("");
            if (mentionsACompilation(field.fieldTypeSymbol().descriptorString())
                    || mentionsACompilation(generic)) {
                found.add(field.fieldName().stringValue());
            }
        }
        return List.copyOf(found);
    }
}
