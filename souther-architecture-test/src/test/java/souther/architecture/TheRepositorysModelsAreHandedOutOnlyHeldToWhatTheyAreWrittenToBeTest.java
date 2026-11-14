package souther.architecture;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Compilation;
import souther.test.RepositoryLayout;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.lang.classfile.Attributes;
import java.lang.classfile.ClassModel;
import java.lang.classfile.FieldModel;
import java.lang.classfile.MethodModel;
import java.lang.reflect.AccessFlag;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.TreeSet;
import java.util.stream.Stream;

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
 * A method added to {@code RepositoryModels} or to {@code Model} that returns a compilation, or a
 * collection of them, as it is, is the way back to the choice.
 */
class TheRepositorysModelsAreHandedOutOnlyHeldToWhatTheyAreWrittenToBeTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofEverythingCompiledHere();

    private static final RepositoryLayout REPOSITORY = RepositoryLayout.ofWorkingDirectory();

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
        assertEquals(List.of(),
                handingOutACompilation(COMPILED.read("souther/compiler/conformance/ConformanceCorpus")),
                "a corpus gives a compilation as it is");
        assertEquals(List.of("answered"),
                handingOutACompilation(
                        COMPILED.read("souther/compiler/conformance/ConformanceCorpus$Analysed")),
                "an analysis gives a compilation by a way other than answered()");
    }

    /**
     * What a corpus is written to be refused with is said by its checked-in diagnostics, and no test
     * says it again.
     *
     * <p>A second statement of it answers separately and nothing fails when the two part: the test
     * holding a corpus to a list of its own goes on passing against a corpus that is now refused
     * for something else. A test that needs it asks {@code ConformanceCorpus#refusedWith()}.
     * Found by the name the corpus is written to be refused under, which is the one thing every
     * restatement had, and which no test source has any other reason to write.
     */
    @Test
    void noTestNamesTheCorpusWrittenToBeRefused() {
        String named = "\"booking\"";
        TreeSet<String> restating = new TreeSet<>();
        int read = 0;
        for (Path module : REPOSITORY.modules()) {
            Path tree = REPOSITORY.javaTreeOf(module, "test");
            if (tree == null) {
                continue;
            }
            try (Stream<Path> files = Files.walk(tree)) {
                for (Path each : files.filter(file -> file.toString().endsWith(".java")).toList()) {
                    read++;
                    if (Files.readString(each).contains(named)) {
                        restating.add(REPOSITORY.root().relativize(each).toString());
                    }
                }
            } catch (IOException unreadable) {
                throw new UncheckedIOException(unreadable);
            }
        }
        assertTrue(read > 0, "no test source was read, so this holds for no reason");
        assertEquals(List.of(), List.copyOf(restating),
                "a test names the corpus written to be refused, which is what restating what it"
                        + " is refused with starts as: ask ConformanceCorpus#refusedWith()");
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
        assertEquals(List.of("HELD", "array", "collected", "single"),
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
     * The public methods of the class that return a compilation, or a type holding one, and the
     * public fields that hold one, by name.
     */
    private static List<String> handingOutACompilation(ClassModel model) {
        TreeSet<String> found = new TreeSet<>();
        for (MethodModel method : model.methods()) {
            if (!method.flags().has(AccessFlag.PUBLIC)) {
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
            if (!field.flags().has(AccessFlag.PUBLIC)) {
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
