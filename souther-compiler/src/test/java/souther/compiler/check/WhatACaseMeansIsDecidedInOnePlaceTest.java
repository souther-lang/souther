package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.test.RepositoryLayout;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
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

    /** Read once: what this asks of it does not change between its checks. */
    private static final RepositoryLayout REPOSITORY = RepositoryLayout.ofWorkingDirectory();

    /**
     * Where reading a subject as an optional is part of the answer: where the forms are told apart,
     * which is the point of it, and nowhere else.
     *
     * <p>A reader that needs the form reads the form. An optional's <em>surface</em> rules do differ
     * — an or-pattern is refused over one, {@code Some(x)} opens the element rather than a newtype
     * layer, an arm naming neither carrier is reported as not a case of an optional — and choosing
     * those rules is a second question, not a second answer to this one. It is asked of the space's
     * own arms, so a form the space gains has to be answered by every reader that decides by form
     * rather than falling into whichever reading is written last.
     */
    private static final List<String> MAY_READ_AN_OPTIONAL_SUBJECT =
            List.of("check/CaseSpace.java");

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


    /** The one file that says a set of values in the model's own names, and the one that reads it. */
    private static final String NAMES_THEM = "check/CoveringNames.java";
    private static final List<String> MAY_READ_THE_NAMES = List.of("check/MatchElaborator.java");

    /**
     * Naming a set of values the way the model declares them is only ever for a report.
     *
     * <p>#966 was a check decided over the cases a declaration listed while everything else read the
     * values under them. The check reads the values now, and what is left of the old reading is a
     * report: what no arm answered for is said in the model's own names, because a model that gave a
     * group of cases a type of its own wrote that type to say something.
     *
     * <p>Which is a reading that must not come back the other way. A check that asked for the
     * declared names and then decided over what came back would be #966 again, arrived at through a
     * helper written for a message — and it would look reasonable at the call, because the names are
     * the ones the author wrote.
     *
     * <p>What this sees is the file that reads it and not what that file does with it. The reader is
     * where the report is composed and also where the check is, so a use inside a check is not
     * visible here; what is visible is the reading spreading to a pass that has no report to write,
     * which is the step that would have to come first.
     */
    @Test
    void namingValuesTheWayTheModelDeclaresThemIsOnlyForAReport() throws IOException {
        List<Path> sources = mainSources();
        assertTrue(sources.size() > 20,
                () -> "the scan found only " + sources.size() + " sources, which is not the tree");

        List<String> readers = new ArrayList<>();
        boolean found = false;
        for (Path source : sources) {
            String where = where(source);
            if (where.equals(NAMES_THEM)) {
                found = true;
                continue;
            }
            if (Files.readString(source, StandardCharsets.UTF_8).contains("CoveringNames")) {
                readers.add(where);
            }
        }
        assertTrue(found, "the file this rule is about moved, so it was asked of nothing");
        assertEquals(MAY_READ_THE_NAMES, readers.stream().sorted().toList(),
                "a set of values is said in the model's names to report it; a pass reading them to"
                        + " decide with is deciding over what a declaration listed, which is #966");
    }

    /** The module-relative name a rule is written against: {@code check/CaseSpace.java}. */
    private static String where(Path source) {
        return source.getParent().getFileName() + "/" + source.getFileName();
    }

    private static List<Path> mainSources() throws IOException {
        return REPOSITORY.mainJavaSources();
    }
}
