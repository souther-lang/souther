package souther.test;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * That the ADR index names every ADR this repository holds, once, and nothing else.
 *
 * <p>An ADR exists because its file does: {@code docs/adr/NNNN-*.md}, as git holds it. The table in
 * {@code docs/adr/README.md} is a second account of the same set, written by hand, and a commit can
 * add to one and not the other. So the relation between them is held here as one relation and
 * asked once: every file has exactly one row, every row names a file, and the number a row shows is
 * the number its file is called by. A row whose number and file disagree satisfies the first two
 * and still sends a reader looking for one ADR to another.
 *
 * <p>Rows are counted rather than collected into a set, because a set would read two rows for one
 * ADR as one.
 *
 * <p>Nothing about the order of the rows, whether the numbers run without a gap, or what the other
 * columns say. Those are how the index is laid out, not which ADRs it names.
 */
class EveryAdrTheRepositoryHoldsIsIndexedExactlyOnceTest {

    private static final RepositoryLayout REPOSITORY = RepositoryLayout.ofWorkingDirectory();

    private static final Path ADRS = Path.of("docs", "adr");

    private static final Path INDEX = ADRS.resolve("README.md");

    /** What makes a file in {@link #ADRS} an ADR: its number, then its name. */
    private static final Pattern ADR = Pattern.compile("(\\d{4})-[^/]+\\.md");

    /**
     * A row of the index: the number it shows, linked to the file it names.
     *
     * <p>This reads the table as it is written today and is not the rule. A line of the table it
     * cannot read is reported rather than passed over, so a row written some other way is never an
     * ADR this quietly stopped counting.
     */
    private static final Pattern ROW = Pattern.compile("^\\|\\s*\\[(\\d{4})\\]\\(([^)\\s]+)\\)\\s*\\|");

    /** The table's own header and the line under it, which are table lines and name no ADR. */
    private static final Pattern HEADING = Pattern.compile("^\\|\\s*(ADR|-+)\\s*\\|");

    @Test
    void theIndexNamesEveryAdrExactlyOnceAndNothingElse() throws IOException {
        GitIndex git = GitIndex.of(REPOSITORY);
        List<Path> adrs = git.trackedFiles().stream()
                .filter(each -> ADRS.equals(each.getParent())
                        && ADR.matcher(each.getFileName().toString()).matches())
                .toList();
        assertFalse(adrs.isEmpty(),
                "git holds no ADR under " + ADRS + ", so there is nothing for the index to name and"
                        + " this would hold either way");

        Map<Path, Integer> rows = new TreeMap<>();
        List<String> problems = new ArrayList<>();
        for (String line : Files.readAllLines(git.resolve(INDEX), StandardCharsets.UTF_8)) {
            if (!line.startsWith("|") || HEADING.matcher(line).find()) {
                continue;
            }
            Matcher row = ROW.matcher(line);
            if (!row.find()) {
                problems.add("a row this cannot read an ADR from: " + line);
                continue;
            }
            Path named = ADRS.resolve(row.group(2)).normalize();
            rows.merge(named, 1, Integer::sum);
            Matcher file = ADR.matcher(named.getFileName().toString());
            if (!file.matches() || !file.group(1).equals(row.group(1))) {
                problems.add("a row shows " + row.group(1) + " and names " + named);
            }
        }

        for (Path adr : adrs) {
            int count = rows.getOrDefault(adr, 0);
            if (count == 0) {
                problems.add("missing from the index: " + adr);
            } else if (count > 1) {
                problems.add("indexed " + count + " times: " + adr);
            }
        }
        for (Path named : rows.keySet()) {
            if (!adrs.contains(named)) {
                problems.add("the index names an ADR git does not hold: " + named);
            }
        }

        assertEquals(List.of(), problems,
                INDEX + " does not name exactly the ADRs this repository holds");
    }
}
