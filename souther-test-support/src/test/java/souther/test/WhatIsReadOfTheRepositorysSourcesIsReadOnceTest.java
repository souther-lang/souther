package souther.test;

import org.junit.jupiter.api.Test;

import java.nio.file.Path;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a fork pays to read the repository's Java sources.
 *
 * <p>The sources do not change while a run happens, so which files there are and what they say is
 * decided by how many there are and not by how many checks ask. The count of reads is asked of a
 * reading that says what it touched, because a timing would answer about the machine.
 */
class WhatIsReadOfTheRepositorysSourcesIsReadOnceTest {

    private static final RepositoryLayout REPOSITORY = RepositoryLayout.ofWorkingDirectory();

    @Test
    void the_working_directorys_repository_is_one_layout_however_often_it_is_asked_for() {
        assertSame(REPOSITORY, RepositoryLayout.ofWorkingDirectory());
    }

    @Test
    void a_layout_made_from_a_path_is_its_own() {
        assertNotSame(REPOSITORY, RepositoryLayout.of(REPOSITORY.root()),
                "a layout made from a path shared the working directory's, so what one holds the"
                        + " other would answer with");
    }

    @Test
    void the_files_of_a_suffix_are_walked_once() {
        assertSame(REPOSITORY.filesUnderSourceTrees(".java"), REPOSITORY.filesUnderSourceTrees(".java"));
        assertSame(REPOSITORY.mainJavaSources(), REPOSITORY.mainJavaSources());
    }

    @Test
    void a_suffix_is_answered_for_itself_and_not_for_the_one_asked_first() {
        List<Path> java = REPOSITORY.filesUnderSourceTrees(".java");
        List<Path> sou = REPOSITORY.filesUnderSourceTrees(".sou");

        assertTrue(java.stream().allMatch(each -> each.toString().endsWith(".java")));
        assertTrue(sou.stream().allMatch(each -> each.toString().endsWith(".sou")));
    }

    @Test
    void the_text_of_every_main_source_is_read_once_however_often_it_is_asked_for() {
        AtomicInteger reads = new AtomicInteger();
        RepositoryJavaSources sources = new RepositoryJavaSources(REPOSITORY, each -> {
            reads.incrementAndGet();
            return each.getFileName().toString();
        });

        Map<Path, String> first = sources.mainTexts();
        int afterOne = reads.get();
        Map<Path, String> again = sources.mainTexts();

        assertEquals(REPOSITORY.mainJavaSources().size(), afterOne,
                "a main source was read other than once");
        assertSame(first, again);
        assertEquals(afterOne, reads.get(), "the second ask read a file again");
        assertEquals(REPOSITORY.mainJavaSources(), List.copyOf(first.keySet()),
                "the texts are in the order the layout names the files");
    }
}
