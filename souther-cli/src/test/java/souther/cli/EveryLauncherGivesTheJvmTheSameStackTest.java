package souther.cli;

import org.junit.jupiter.api.Test;
import souther.test.RepositoryLayout;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The stack is what holds the bound on what a definition may say
 * ([#source-structural-complexity-is-bounded]): every phase descends what it builds by recursion,
 * and a source at the bound needs about a megabyte, which is more than a platform's default on some
 * of the platforms this runs on. A launcher that gave the JVM less would refuse a source the
 * compiler supports, and would refuse it only where that launcher is the one in use.
 *
 * <p>Each distribution reaches the JVM through a launcher of its own — a shell script, a batch file,
 * and the options an image is built with — and a launcher may reach it from more than one line.
 * Nothing makes any of them agree, so this reads every place a stack is handed over and says when
 * they stop agreeing.
 *
 * <p>What a comment says about the flag is not the flag. A launcher that explains the stack in prose
 * names the size there too, and a file read for the first thing that looks like the flag is read at
 * its explanation — which goes on saying the old size after the line below it was changed. So
 * comments are dropped before anything is read out.
 */
class EveryLauncherGivesTheJvmTheSameStackTest {

    private static final Pattern STACK = Pattern.compile("-Xss(\\d+[kmgKMG]?)");
    private static final Pattern COMMENT = Pattern.compile("^\\s*(#|rem\\s|rem$).*", Pattern.CASE_INSENSITIVE);

    @Test
    void everyLineThatHandsTheJvmAStackHandsItTheSameOne() throws Exception {
        Path root = RepositoryLayout.ofWorkingDirectory().root();
        Map<Path, Set<String>> stated = new LinkedHashMap<>();
        for (Path launcher : List.of(
                root.resolve("souther-cli/src/main/launcher/souther"),
                root.resolve("souther-cli/src/main/launcher/souther.cmd"),
                root.resolve("bin/package-windows.ps1"))) {
            assertTrue(Files.isRegularFile(launcher), launcher + " is where a launcher is written");
            Set<String> said = stacksGivenBy(Files.readString(launcher));
            assertTrue(!said.isEmpty(), launcher.getFileName() + " gives the JVM no stack outside its"
                    + " comments, so a source at the supported bound is refused wherever it is the"
                    + " launcher in use");
            stated.put(launcher, said);
        }

        Set<String> distinct = new LinkedHashSet<>();
        stated.values().forEach(distinct::addAll);
        assertEquals(1, distinct.size(), "the launchers hand the JVM different stacks, so what the"
                + " compiler accepts depends on which one ran: " + stated);
    }

    private static Set<String> stacksGivenBy(String launcher) {
        Set<String> given = new LinkedHashSet<>();
        for (String line : launcher.split("\\R")) {
            if (COMMENT.matcher(line).matches()) {
                continue;
            }
            Matcher said = STACK.matcher(line);
            while (said.find()) {
                given.add(said.group(1));
            }
        }
        return given;
    }
}
