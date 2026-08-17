package souther.compiler.check;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which cases a subject has, and what a value turns out to be once it is one of them, is worked out
 * where the subject's cases are and nowhere else.
 *
 * <p>{@code Core}'s own contract says a construct the backend used to re-detect becomes a node
 * rather than a shape read a second time. Case dispatch had not caught up: the emitter asked whether
 * a subject was an optional, whether an arm named one case or several, and whether a case was a
 * primitive, each time it wrote an arm, and a third reader in the checker asked the same questions
 * its own way. Three readings of one thing agree until the day one of them is extended.
 *
 * <p>So {@code CaseSpace} answers it once, a {@code CaseSelector} carries the answer, and everything
 * downstream reads the selector. This is asked of the sources: a tripwire and not a proof — a helper
 * in between defeats it — but the line that would have to be added first is the one it fails on.
 */
class WhatACaseMeansIsDecidedInOnePlaceTest {

    /**
     * Where reading a subject as an optional is still part of the answer.
     *
     * <p>{@code CaseSpace} is where the three forms are told apart, which is the point of it. The
     * elaborator reads it once more, and that one is not the same question: an optional's
     * <em>surface</em> rules differ — an or-pattern is refused over one, {@code Some(x)} opens the
     * element rather than a newtype layer, and an arm naming neither carrier is reported as not a
     * case of an optional. Which rules the text is held to is decided there; what a case means is not.
     */
    private static final List<String> MAY_READ_AN_OPTIONAL_SUBJECT =
            List.of("check/CaseSpace.java", "check/MatchElaborator.java");

    /**
     * Files that take a {@code match} apart. Anything reading a subject's shape here would be
     * deciding what an arm selects or binds, which is what this test exists to stop.
     */
    private static final List<String> WHERE_A_MATCH_IS_TAKEN_APART =
            List.of("check/CaseSpace.java", "check/MatchElaborator.java", "check/HelperParams.java",
                    "codegen/BodyGen.java", "codegen/CaseGen.java");

    @Test
    void onlyTheCasesOfASubjectDecideWhetherItIsAnOptional() throws IOException {
        List<String> seen = new ArrayList<>();
        List<String> readers = new ArrayList<>();
        for (Path source : mainSources()) {
            String where = where(source);
            if (!WHERE_A_MATCH_IS_TAKEN_APART.contains(where)) {
                continue;
            }
            seen.add(where);
            if (Files.readString(source, StandardCharsets.UTF_8).contains("instanceof Type.OptionOf")) {
                readers.add(where);
            }
        }
        assertEquals(WHERE_A_MATCH_IS_TAKEN_APART.stream().sorted().toList(),
                seen.stream().sorted().toList(),
                "the files this rule is about moved or were renamed, so it was asked of nothing");
        assertEquals(MAY_READ_AN_OPTIONAL_SUBJECT.stream().sorted().toList(),
                readers.stream().sorted().toList(),
                "what a case means comes from CaseSpace; a match reader asking the subject's shape"
                        + " again is deciding it a second time");
    }

    @Test
    void theEmitterNeverAsksHowManyCasesAnArmNames() throws IOException {
        int emitters = 0;
        List<String> askers = new ArrayList<>();
        for (Path source : mainSources()) {
            String where = where(source);
            if (!where.startsWith("codegen/")) {
                continue;
            }
            emitters++;
            String text = Files.readString(source, StandardCharsets.UTF_8);
            if (text.contains("caseTypes().size()") || text.contains("caseTypes().get(0)")) {
                askers.add(where);
            }
        }
        assertTrue(emitters > 5, "the emitters moved out of codegen, so this was asked of nothing");
        assertEquals(List.of(), askers,
                "an arm's selectors and what it binds are on its resolved pattern; counting the"
                        + " names it wrote is working out what the checker already answered");
    }

    /** The module-relative name a rule is written against: {@code check/CaseSpace.java}. */
    private static String where(Path source) {
        return source.getParent().getFileName() + "/" + source.getFileName();
    }

    private static List<Path> mainSources() throws IOException {
        Path module = Path.of("").toAbsolutePath();
        Path repo = Files.isDirectory(module.resolve(Path.of("src", "main", "java")))
                ? module.getParent() : module;
        List<Path> sources = new ArrayList<>();
        try (Stream<Path> modules = Files.list(repo)) {
            for (Path candidate : modules.toList()) {
                Path root = candidate.resolve(Path.of("src", "main", "java"));
                if (!Files.isDirectory(root)) {
                    continue;
                }
                try (Stream<Path> walk = Files.walk(root)) {
                    walk.filter(p -> p.toString().endsWith(".java")).forEach(sources::add);
                }
            }
        }
        assertFalse(sources.isEmpty(), "found no sources at all — the scan missed the tree");
        return sources;
    }
}
