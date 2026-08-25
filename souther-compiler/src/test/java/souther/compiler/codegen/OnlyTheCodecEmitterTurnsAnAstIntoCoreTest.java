package souther.compiler.codegen;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.lang.classfile.ClassFile;
import java.lang.classfile.constantpool.ClassEntry;
import java.lang.classfile.constantpool.PoolEntry;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * One type in this package turns an AST expression into Core, and it is the codec emitter's.
 *
 * <p>What the boundary is for. A backend that elaborates is a backend deciding what an expression
 * means, which is the checker's answer and nobody else's (ADR-0021, issue #81); a data's invariant
 * and a behavior's rule were being decided that way until #1080. A decoder and an encoder are still
 * written as AST when they reach here and are the named exception, so what this holds is that the
 * exception has one owner rather than being a method anybody in reach can call.
 *
 * <p>A tripwire over the direct references and not a reachability proof. What it reads is which
 * class files of this package name the elaborator in their constant pool, so a call made through
 * something else in this package would not be one of them. What closes that today is the shape
 * rather than this: the way in is a private nested class of the owner, so there is nothing for
 * another emitter here to call, and {@link BodyGen} takes Core. This holds the day somebody writes
 * the call again in a place of their own.
 */
class OnlyTheCodecEmitterTurnsAnAstIntoCoreTest {

    /** The elaborator, as a class file names it. */
    private static final String ELABORATOR = "souther/compiler/check/Elaborator";

    /** The codec emitter and the nested type it keeps the AST path in. */
    private static final String OWNER = "CodecGen";

    @Test
    void onlyTheCodecEmitterNamesTheElaborator() throws IOException {
        List<String> reaching = new ArrayList<>();
        for (Path each : classFiles()) {
            if (names(each, ELABORATOR)) {
                reaching.add(each.getFileName().toString());
            }
        }

        assertTrue(reaching.stream().allMatch(name -> name.startsWith(OWNER)),
                "an AST becomes Core in the codec emitter and nowhere else in this package, and "
                        + reaching + " names the elaborator");
        assertEquals(1, reaching.size(),
                "and in one place inside it, which is " + reaching);
    }

    /** And the walk above found something to read, so an empty answer is not a passing one. */
    @Test
    void andTheWalkReadsThisPackagesClasses() throws IOException {
        assertTrue(classFiles().size() > 10, "the emitters are there to be read");
    }

    private static List<Path> classFiles() throws IOException {
        Path built = Path.of(
                OnlyTheCodecEmitterTurnsAnAstIntoCoreTest.class.getProtectionDomain()
                        .getCodeSource().getLocation().getPath())
                .getParent()
                .resolve("classes/souther/compiler/codegen");
        try (Stream<Path> found = Files.list(built)) {
            return found.filter(path -> path.toString().endsWith(".class")).toList();
        }
    }

    /** Whether {@code classFile} names {@code type} anywhere in its constant pool. */
    private static boolean names(Path classFile, String type) throws IOException {
        var parsed = ClassFile.of().parse(Files.readAllBytes(classFile));
        for (PoolEntry entry : parsed.constantPool()) {
            if (entry instanceof ClassEntry named && named.name().stringValue().equals(type)) {
                return true;
            }
        }
        return false;
    }
}
