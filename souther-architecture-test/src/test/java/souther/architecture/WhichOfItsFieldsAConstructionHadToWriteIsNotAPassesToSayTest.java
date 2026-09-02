package souther.architecture;

import souther.compiler.ast.Hir;
import souther.test.RepositoryLayout;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.lang.classfile.ClassFile;
import java.lang.classfile.constantpool.MemberRefEntry;
import java.lang.classfile.constantpool.PoolEntry;
import java.lang.reflect.Constructor;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a construction had to write out every field it has is what the reading of its source
 * settled, and no pass says it for one.
 *
 * <p>The answer is a value of a type declared where only {@code souther.compiler.ast} can name it,
 * so a pass elsewhere cannot spell one. What javac cannot refuse is a pass taking the answer off a
 * node and handing it to another, or reading it to decide something of its own — either of which
 * puts the answer somewhere other than the node that was read. So nothing outside the package names
 * it at all: the check that reads it asks the node a question ({@code mayOmitOptionalFields}), and
 * the passes that rebuild one carry what they were handed.
 *
 * <p>Read off the compiled classes and not the source, because it is a rule about who names what: a
 * reference is in the constant pool of the class that makes it whatever the call looks like. This is
 * the companion of {@link WhereAConstructionCameFromIsNotAPassesToWriteTest}, which asks the same
 * question of where a construction came from — the other answer settled at the same reading.
 *
 * <p>The population is the whole repository, which that test asserts is built when these run.
 */
class WhichOfItsFieldsAConstructionHadToWriteIsNotAPassesToSayTest {

    /** Where the answer may be made, read and handed over. */
    private static final String THEIRS = "souther/compiler/ast/";

    private static final String THE_ANSWER = "L" + Hir.Fields.class.getName().replace('.', '/') + ";";

    private static final RepositoryLayout REPOSITORY = RepositoryLayout.ofWorkingDirectory();

    @Test
    void nothingOutsideTheTreeNamesTheAnswerAtAll() {
        List<String> naming = new ArrayList<>();
        for (Path each : everyCompiledClass()) {
            if (internalName(each).startsWith(THEIRS) || !namesTheAnswerIn(each)) {
                continue;
            }
            naming.add(internalName(each));
        }

        assertEquals(List.of(), naming.stream().sorted().toList(),
                "what a construction had to write is the reading's answer and the node's to keep:"
                        + " a check asks the node whether a field left out is the absent value it"
                        + " declares, and a pass rebuilding one carries the answer it was handed");
    }

    /**
     * One way to make a construction from its parts, so none of them fills the answer in.
     *
     * <p>A second constructor is how the answer came to be invented: one taking every component is
     * what a reading and a rebuild both go through, and one taking fewer decides for its caller what
     * the rest are. The named entry points are what a caller reaches for instead, and each says what
     * it is answering and out of what.
     */
    @Test
    void andAConstructionIsMadeFromItsPartsInOneWay() {
        List<String> constructors = new ArrayList<>();
        for (Constructor<?> each : Hir.NewData.class.getDeclaredConstructors()) {
            constructors.add(each.getParameterCount() + " parameters");
        }

        assertEquals(List.of(Hir.NewData.class.getRecordComponents().length + " parameters"),
                constructors,
                "a constructor taking fewer than every component answers for its caller: what to"
                        + " add instead is an entry point named for what it is answering out of");
    }

    /** The control: the walk reads the classes it is about, and sees the naming it forbids where it
     *  is not forbidden at all — inside the package, where the answer is made and read. */
    @Test
    void andTheCheckSeesWhatItIsLookingForWhereThatIsAllowed() {
        assertTrue(everyCompiledClass().stream()
                        .filter(each -> internalName(each).startsWith(THEIRS))
                        .anyMatch(WhichOfItsFieldsAConstructionHadToWriteIsNotAPassesToSayTest
                                ::namesTheAnswerIn),
                "the package that owns the answer names it, which is what this reads");
    }

    /** Whether {@code compiled} names anything that takes or answers with the answer — which
     *  includes naming one of its constants, whose descriptor is the type. */
    private static boolean namesTheAnswerIn(Path compiled) {
        try {
            for (PoolEntry entry : ClassFile.of().parse(Files.readAllBytes(compiled))
                    .constantPool()) {
                if (entry instanceof MemberRefEntry member
                        && member.type().stringValue().contains(THE_ANSWER)) {
                    return true;
                }
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        return false;
    }

    /** The class's own binary name, read off the file's place under its module's build directory. */
    private static String internalName(Path compiled) {
        String path = compiled.toString().replace('\\', '/');
        int at = path.indexOf("/classes/");
        int from = at < 0 ? path.indexOf("/test-classes/") + "/test-classes/".length()
                : at + "/classes/".length();
        return path.substring(from, path.length() - ".class".length());
    }

    /** Every class of every module of this build, main and test alike. */
    private static List<Path> everyCompiledClass() {
        List<Path> out = new ArrayList<>();
        for (Path module : REPOSITORY.modules()) {
            for (String built : List.of("classes", "test-classes")) {
                Path where = module.resolve("target").resolve(built);
                if (!Files.isDirectory(where)) {
                    continue;
                }
                try (Stream<Path> found = Files.walk(where)) {
                    out.addAll(found.filter(p -> p.toString().endsWith(".class")).toList());
                } catch (IOException e) {
                    throw new UncheckedIOException(e);
                }
            }
        }
        return out;
    }
}
