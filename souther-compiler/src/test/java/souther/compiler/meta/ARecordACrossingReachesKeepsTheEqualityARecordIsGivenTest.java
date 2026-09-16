package souther.compiler.meta;

import org.junit.jupiter.api.Test;

import souther.compiler.crossing.ObjectEqualityIsTheCrossingAnswer;
import souther.compiler.values.Apartness;

import java.io.IOException;
import java.io.InputStream;
import java.io.UncheckedIOException;
import java.net.URISyntaxException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.stream.Stream;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.Instruction;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeDynamicInstruction;
import java.util.ArrayList;
import java.util.List;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A record a crossing reaches keeps the equality a record is given.
 *
 * <p>The reading that decides whether a collection may hold a value walks a record's components and
 * asks about each, because a record is its components and nothing else. That rests on the record
 * comparing by them — which is what a record does and not what a record must do. One can write an
 * equality out and read whatever its writer chose, and the components would then be answering for
 * something the record does not do: a set could hold apart what this comparison holds together, and
 * every component would have passed.
 *
 * <p><b>Not something a reading of the class can tell.</b> The equality a record is given is
 * declared by the record like a written one, takes the same argument and answers the same type. It
 * is told apart by how it is compiled — the given one is left to be linked against the runtime's
 * own way of comparing records — so this is asked of the class file.
 *
 * <p>Asked of the records a crossing can reach, which is the population the reading is over. Wider
 * than that it would be asking about records whose equality this comparison never consults, and
 * each would need an account written for a question nobody put to it.
 */
class ARecordACrossingReachesKeepsTheEqualityARecordIsGivenTest {

    /** What a record's given equality is left to be linked against. */
    private static final String THE_GIVEN_ONE = "java/lang/runtime/ObjectMethods";

    @Test
    void everyRecordThatSaysACollectionMayHoldItKeepsTheEqualityARecordIsGiven() {
        List<String> writingTheirOwn = new ArrayList<>(new TreeSet<>(
                recordsThatSayACollectionMayHoldThem().stream()
                        .filter(form -> !keepsTheGivenEquality(form))
                        .map(Class::getName).toList()));

        assertEquals(List.of(), writingTheirOwn,
                "a record a crossing reaches is read as its components by the reading that decides"
                        + " what a collection may hold, and one comparing by something else is read"
                        + " as components that do not decide it");
    }

    /**
     * The records that say a collection may hold them, read off the compiled classes.
     *
     * <p>The population is exactly what the reading can be handed. A set holds whatever a
     * declaration put in it, and what a part is declared to hold says nothing about what arrives
     * there — which is why that reading is made of values at all — so a population taken from the
     * forms a crossing is known to reach would be smaller than the one the reading answers about,
     * and a record outside it would have its components read with nobody having looked at its
     * equality. Taken from what says it, the two are one set.
     */
    private static List<Class<?>> recordsThatSayACollectionMayHoldThem() {
        List<Class<?>> saying = new ArrayList<>();
        Path classes = whereTheClassesAre();
        try (Stream<Path> found = Files.walk(classes)) {
            for (Path file : found.filter(one -> one.toString().endsWith(".class")).toList()) {
                String named = classes.relativize(file).toString()
                        .replace(java.io.File.separatorChar, '.').replaceAll("\\.class$", "");
                Class<?> read;
                try {
                    read = Class.forName(named, false,
                            ARecordACrossingReachesKeepsTheEqualityARecordIsGivenTest.class
                                    .getClassLoader());
                } catch (ClassNotFoundException | LinkageError e) {
                    continue;   // not this module's to answer about
                }
                if (read.isRecord()
                        && ObjectEqualityIsTheCrossingAnswer.class.isAssignableFrom(read)) {
                    saying.add(read);
                }
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        return saying;
    }

    private static Path whereTheClassesAre() {
        try {
            return Path.of(DeclarationAgreement.class.getProtectionDomain().getCodeSource()
                    .getLocation().toURI());
        } catch (URISyntaxException e) {
            throw new IllegalStateException("the classes this module compiled are somewhere", e);
        }
    }

    /**
     * The control: there are records in the population, and this reading can say no about one.
     *
     * <p>Both halves. A reading that found no record would report nothing and say nothing; a
     * reading that said yes to everything would report nothing either. The one it is asked to say
     * no about is not a record a crossing reaches — it is an edge of an apartness, which this
     * comparison never meets — and it is here because it is a record of this repository that really
     * does write its own equality, rather than one written to fail.
     */
    @Test
    void andTheReadingWouldSeeARecordThatWritesItsOwn() {
        assertFalse(recordsThatSayACollectionMayHoldThem().isEmpty(),
                "records say it, so the sweep above has something to be about");

        assertFalse(recordsThatSayACollectionMayHoldThem().contains(Apartness.Edge.class),
                "it says nothing, so nothing here is about what the comparison does today");
        assertFalse(keepsTheGivenEquality(Apartness.Edge.class),
                "and it writes its own equality, which is what this reading has to be able to see");
    }

    /**
     * Whether what the record answers {@code equals} with is left to be linked against the
     * runtime's way of comparing records.
     *
     * <p>Read off that method and not off the class. A record whose equality is written out still
     * has the number and the printing a record is given, and both are left to the same place — so a
     * reading that asked whether the class names it at all would call every record safe, whatever
     * its equality does.
     */
    private static boolean keepsTheGivenEquality(Class<?> form) {
        for (MethodModel method : classFileOf(form).methods()) {
            if (!"equals".equals(method.methodName().stringValue())
                    || !"(Ljava/lang/Object;)Z".equals(method.methodType().stringValue())) {
                continue;
            }
            return instructionsOf(method).stream().anyMatch(
                    ARecordACrossingReachesKeepsTheEqualityARecordIsGivenTest::leftToTheGivenOne);
        }
        return false;
    }

    /** Whether this instruction is the call left to be linked against that way of comparing. */
    private static boolean leftToTheGivenOne(Instruction instruction) {
        return instruction instanceof InvokeDynamicInstruction dynamic
                && THE_GIVEN_ONE.equals(dynamic.invokedynamic().bootstrap().bootstrapMethod()
                        .reference().owner().name().stringValue());
    }

    private static List<Instruction> instructionsOf(MethodModel method) {
        return method.code().map(code -> code.elementList().stream()
                .filter(Instruction.class::isInstance)
                .map(Instruction.class::cast)
                .toList()).orElse(List.of());
    }

    private static ClassModel classFileOf(Class<?> form) {
        String where = "/" + form.getName().replace('.', '/') + ".class";
        try (InputStream bytes = form.getResourceAsStream(where)) {
            if (bytes == null) {
                throw new IllegalStateException("no class file for " + form.getName());
            }
            return ClassFile.of().parse(bytes.readAllBytes());
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }
}
