package souther.architecture;

import org.junit.jupiter.api.Test;

import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The walks over compiled classes read more than one module.
 *
 * <p>Every rule here that lists who names a member reads {@link CompiledOutputs}, and a list of
 * rows compared against an expectation still matches when the walk read fewer modules than the
 * repository has. A module that has sources and left no classes is refused where the outputs are
 * taken; what is left to ask is that the repository's modules were found at all, which is asked
 * once here for every rule that reads them.
 */
class EveryModuleTheRepositoryHoldsIsReadTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    @Test
    void theClassesReadAreInMoreThanOneModule() {
        int read = 0;
        for (Path module : COMPILED.modules()) {
            if (!COMPILED.classesOf(module).isEmpty()) {
                read++;
            }
        }
        assertTrue(read > 1, "a rule that lists who names a member is answering about every module"
                + " that could name it, and the walk found classes in " + read);
    }
}
