package souther.compiler.diag;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A diagnostic that names a second file is telling a reader where to look. Two files a compile was
 * handed that would be shown the same name tell them nothing, which is what naming the file was for.
 */
class NoTwoFilesReadTheSameTest {

    @Test
    void oneFileKeepsItsBasename() {
        assertEquals(List.of("model.sou"), SourceNames.of(List.of("/tmp/build/model.sou")));
    }

    @Test
    void filesThatDifferInTheirLastSegmentKeepTheirBasenames() {
        assertEquals(List.of("model.sou", "rules.sou"),
                SourceNames.of(List.of("a/model.sou", "b/rules.sou")));
    }

    @Test
    void filesSharingABasenameAreNamedByAsMuchOfThePathAsItTakes() {
        assertEquals(List.of("domain-a/model.sou", "domain-b/model.sou"),
                SourceNames.of(List.of("src/domain-a/model.sou", "src/domain-b/model.sou")));
    }

    @Test
    void aSharedTailIsWalkedBackUntilSomethingDiffers() {
        assertEquals(List.of("one/domain/model.sou", "two/domain/model.sou"),
                SourceNames.of(List.of("one/domain/model.sou", "two/domain/model.sou")));
    }

    @Test
    void aPathThatSharesEveryTailKeepsItsWholeSelf() {
        assertEquals(List.of("a/model.sou", "a/model.sou"),
                SourceNames.of(List.of("a/model.sou", "a/model.sou")),
                "the same file twice is the same name twice; there is nothing to tell apart");
    }

    @Test
    void aWindowsPathIsSplitOnItsOwnSeparator() {
        assertEquals(List.of("domain-a\\model.sou".replace('\\', '/'),
                        "domain-b\\model.sou".replace('\\', '/')),
                SourceNames.of(List.of("src\\domain-a\\model.sou", "src\\domain-b\\model.sou")));
    }
}
