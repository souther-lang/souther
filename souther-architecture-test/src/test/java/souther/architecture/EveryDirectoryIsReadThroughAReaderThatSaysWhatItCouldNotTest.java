package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeInstruction;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a directory holds is read through {@code ConfinedTree.walk} or {@code Listing}, and through
 * nothing else.
 *
 * <p>Each of the ways {@link java.nio.file.Files} offers has a way of saying nothing about what it
 * could not read. {@code Files.list}, {@code Files.walk} and {@code Files.find} throw an unchecked
 * exception out of the middle of a stream, past the {@code catch (IOException)} written around them
 * to say what an unreadable directory means; a {@code DirectoryStream} does the same from its
 * iterator; and {@code Files.walkFileTree} with a {@code SimpleFileVisitor} passes over whatever
 * reaches a callback the visitor did not write. Each was found doing so: a tree of sources compiled
 * from the part that could be read, and a language server that failed every snapshot of a workspace
 * holding a directory it could not open (souther-lang/souther-wasm-compiler#55,
 * souther-lang/souther#2342). The two readers here say what they could not read, and a caller says
 * what that means to it.
 *
 * <p>Read off the compiled classes of what this repository publishes, so a call is a row however it
 * is spelled.
 */
class EveryDirectoryIsReadThroughAReaderThatSaysWhatItCouldNotTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    private static final String FILES = "java/nio/file/Files";

    /** Each way of reading a directory, and the one class that may call it. */
    private static final Map<String, String> READ_ONLY_BY = Map.of(
            "list", "",
            "walk", "",
            "find", "",
            "walkFileTree", "souther/compiler/io/ConfinedTree",
            "newDirectoryStream", "souther/compiler/io/Listing");

    /**
     * The test support, which a build's tests run on: a directory it cannot read fails the test
     * that asked, which is what a test is for, and nothing it says reaches a user.
     */
    private static final String TEST_SUPPORT = "souther/test/";

    @Test
    void noDirectoryIsReadAroundTheReaders() {
        Set<String> found = new TreeSet<>();
        List<String> callers = new ArrayList<>();
        for (ClassModel each : COMPILED.all()) {
            String owner = each.thisClass().asInternalName();
            if (owner.startsWith(TEST_SUPPORT)) {
                continue;
            }
            for (MethodModel method : each.methods()) {
                method.code().ifPresent(code -> code.elementStream()
                        .filter(InvokeInstruction.class::isInstance)
                        .map(InvokeInstruction.class::cast)
                        .filter(call -> call.owner().asInternalName().equals(FILES))
                        .forEach(call -> {
                            String reading = call.name().stringValue();
                            if (!READ_ONLY_BY.containsKey(reading)) {
                                return;
                            }
                            String where = owner + "." + method.methodName().stringValue();
                            callers.add(where);
                            String allowed = READ_ONLY_BY.get(reading);
                            if (!(owner.equals(allowed) || owner.startsWith(allowed + "$"))
                                    || allowed.isEmpty()) {
                                found.add(where + " calls Files." + reading);
                            }
                        }));
            }
        }

        // The walk saw both readers' own calls, so an empty answer is not a walk that read nothing.
        assertTrue(callers.stream().anyMatch(it -> it.startsWith("souther/compiler/io/ConfinedTree.")),
                "the walk over the classes reached ConfinedTree");
        assertTrue(callers.stream().anyMatch(it -> it.startsWith("souther/compiler/io/Listing.")),
                "the walk over the classes reached Listing");
        assertEquals(Set.of(), found,
                "a directory read around ConfinedTree.walk and Listing says nothing of what it"
                        + " could not read");
    }
}
