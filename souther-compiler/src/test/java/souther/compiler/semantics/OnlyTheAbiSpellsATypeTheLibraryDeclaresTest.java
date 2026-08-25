package souther.compiler.semantics;

import souther.compiler.DefaultStdlib;
import souther.compiler.Reserved;
import souther.compiler.ast.Hir;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The library declares its types, and nothing else in this compiler says their names.
 *
 * <p>ADR-0087 puts it as a rule: the declaration is where a runtime-backed type is settled, and no
 * other place may branch on its name. A conditional that asks whether a type is called
 * {@code RoundingMode} is a second answer to which type that is — one the library does not know it
 * has given, and one that goes on answering after the library has changed its mind.
 *
 * <p>{@code semantics/Arithmetic} had one, and it is what #1039 was. A rule there says a position
 * of {@code Decimal.divide} reads a rounding policy; which type answers to that is a question about
 * the library and is asked where the library is, by taking the type {@code Decimal.round} declares
 * at its own policy position. Two declarations held to each other, and no name written down.
 *
 * <p>One place spells them, and has to: {@code jvm.SoutherJvmAbi} says what each is called on this
 * backend, and a table from a declaration to a class name is names on both sides. That is the seam
 * #1038 built, and it is the only exception here.
 *
 * <p>Read off the library rather than listed, so a type the library gains is covered the day it is
 * declared.
 */
class OnlyTheAbiSpellsATypeTheLibraryDeclaresTest {

    /** Where a declaration may be named, because naming it is the answer being given. */
    private static final Set<String> THE_ABI = Set.of("jvm/SoutherJvmAbi.java");

    @Test
    void nothingButTheAbiWritesOneOfTheirNames() throws IOException {
        Set<String> declared = everyTypeTheLibraryDeclares();
        assertTrue(declared.contains("RoundingMode"),
                () -> "the library declares RoundingMode; this found " + declared);

        Set<String> spelling = new TreeSet<>();
        for (Path source : sources()) {
            String text = Files.readString(source);
            for (String name : declared) {
                if (text.contains('"' + name + '"') && !THE_ABI.contains(relative(source))) {
                    spelling.add(relative(source) + ": \"" + name + '"');
                }
            }
        }

        assertEquals(List.of(), List.copyOf(spelling),
                "which type answers to a rule is the library's to say (ADR-0087); what one is called"
                        + " on a machine is `jvm.SoutherJvmAbi`'s, and is the only name written out");
    }

    /** Every type name the standard library declares, from the library itself. */
    private static Set<String> everyTypeTheLibraryDeclares() {
        Set<String> names = new LinkedHashSet<>();
        for (Reserved.StdlibModule module : Reserved.MODULES) {
            for (Hir.Def def : DefaultStdlib.get()
                    .languageDeclarationsIn(module.moduleName()).values()) {
                names.add(def.name());
            }
        }
        return names;
    }

    private static String relative(Path source) {
        String path = source.toString().replace('\\', '/');
        return path.substring(path.indexOf("souther/compiler/") + "souther/compiler/".length());
    }

    private static List<Path> sources() throws IOException {
        Path main = Path.of("src/main/java/souther/compiler");
        assertTrue(Files.isDirectory(main), () -> "no " + main.toAbsolutePath());
        try (Stream<Path> walk = Files.walk(main)) {
            List<Path> found = walk.filter(each -> each.toString().endsWith(".java")).sorted()
                    .toList();
            assertTrue(found.size() > 100, () -> "that is not the compiler: " + found.size());
            return found;
        }
    }
}
