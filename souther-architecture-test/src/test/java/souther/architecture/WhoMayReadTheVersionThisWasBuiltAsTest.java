package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.constantpool.MemberRefEntry;
import java.lang.classfile.constantpool.PoolEntry;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where which Souther this is enters this compiler.
 *
 * <p>It is in the manifest, which the build fills from the one place the version is written, and
 * every face that answers the question — the command line, the language server, the MCP server, and
 * what a compiled module says it was compiled by — answers the same reader. A face that reads the
 * manifest for itself is a second answer to one question: it chooses its own word for the run that
 * has no manifest, and the two words then differ by which face was asked. That is how the server
 * came to tell an editor a version this compiler is not, and it is not a mistake anybody makes on
 * purpose — a package accessor is three tokens and reads as its own answer.
 *
 * <p><b>What this holds, said exactly.</b> It holds that one class names the accessor. It does not
 * hold that nothing else can find the version out: a manifest is a file in a jar and can be read as
 * one, and no row here would see that. What it closes is the way it was reached twice.
 *
 * <p>Read off the compiled classes rather than the source, so the accessor reached through a method
 * reference is one of these too.
 */
class WhoMayReadTheVersionThisWasBuiltAsTest {

    private static final String OWNER = "java/lang/Package";

    private static final String READING_THE_VERSION = "getImplementationVersion";

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    /**
     * The one class that reads it, and what the rest of them ask instead.
     *
     * <p>{@code ModuleMetadata} holds both the reading and the word for the run that has no
     * manifest, and it holds them beside each other because one caller has to tell the two apart:
     * {@code souther init} writes a version into a build file, where the word this compiler falls
     * back to resolves nothing. Every other face wants the reading with the word already chosen,
     * which is {@code compilerVersion()}.
     */
    private static final List<String> READING_IT =
            List.of("souther/compiler/meta/ModuleMetadata -> " + OWNER + "#" + READING_THE_VERSION);

    @Test
    void everyClassThatReadsTheVersionThisWasBuiltAsIsWrittenDown() {
        assertEquals(READING_IT, new ArrayList<>(reading()),
                "a row added here is a second answer to `which Souther is this`, which is a face"
                        + " that will differ from the others on the run that has no manifest;"
                        + " `ModuleMetadata.compilerVersion()` is the reading with that already"
                        + " settled");
    }

    /**
     * The walk reads every module's classes.
     *
     * <p>Asked of the modules the repository has and not of what a build happened to leave: a module
     * whose classes are missing is one whose calls this cannot see, and the rows from the rest would
     * match and this would pass while answering about fewer modules than it names.
     */
    @Test
    void andEveryModuleTheRepositoryHoldsWasRead() {
        assertTrue(modulesRead() > 1,
                "the classes this reads are in more than the one module that declares the reading");
    }

    /** Every class naming the accessor, as the class and what it named. */
    private static Set<String> reading() {
        Set<String> found = new TreeSet<>();
        for (ClassModel model : COMPILED.all()) {
            for (PoolEntry entry : model.constantPool()) {
                if (entry instanceof MemberRefEntry member
                        && OWNER.equals(member.owner().name().stringValue())
                        && READING_THE_VERSION.equals(member.name().stringValue())) {
                    found.add(model.thisClass().asInternalName() + " -> "
                            + OWNER + "#" + READING_THE_VERSION);
                }
            }
        }
        return found;
    }

    private static int modulesRead() {
        int read = 0;
        for (Path module : COMPILED.modules()) {
            if (COMPILED.mainOutputOf(module).isPresent()) {
                read++;
            }
        }
        return read;
    }
}
