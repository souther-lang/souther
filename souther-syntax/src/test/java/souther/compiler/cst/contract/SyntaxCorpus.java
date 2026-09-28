package souther.compiler.cst.contract;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Stream;

/**
 * The cases of {@code syntax/corpus}, handed out to be swept: every source the contract says
 * something about, with what it says.
 */
final class SyntaxCorpus {

    private SyntaxCorpus() {}

    /** One case of the corpus: a source, and what the contract says of it. */
    record Case(String file, String name, String source, Expected expected) {

        @Override
        public String toString() {
            return file + ": " + name;
        }
    }

    /** What a case says of its source: the tree it is, or that it is not Souther source. */
    sealed interface Expected permits Accepted, Refused {
    }

    record Accepted(ContractTree tree) implements Expected {
    }

    /** Refused, and nothing more: where a reading stops and what it recovers is no contract's. */
    record Refused() implements Expected {
    }

    /** Every case of every corpus file, in the order the files and the cases are written. */
    static List<Case> cases() {
        List<Case> out = new ArrayList<>();
        try (Stream<Path> files = Files.list(SyntaxContract.path("corpus"))) {
            for (Path file : files.filter(f -> f.toString().endsWith(".txt")).sorted().toList()) {
                out.addAll(casesIn(file.getFileName().toString(),
                        Files.readString(file, StandardCharsets.UTF_8)));
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        if (out.isEmpty()) {
            throw new IllegalStateException("the corpus holds no case");
        }
        return out;
    }

    /**
     * The cases one file writes, in tree-sitter's test format: a name between two lines of
     * {@code =}, an optional {@code :error} line under the name, the source, a line of {@code -},
     * and the expected tree.
     *
     * <p>Lines are split at LF alone, so a CR written in a source stays in it: the corpus is where
     * a CR LF and a CR on its own are witnessed, and reading them away would witness nothing.
     */
    static List<Case> casesIn(String file, String text) {
        List<String> lines = List.of(text.split("\n", -1));
        List<Case> out = new ArrayList<>();
        int i = 0;
        while (i < lines.size() && lines.get(i).isBlank()) {
            i++;
        }
        while (i < lines.size()) {
            if (!isRule(lines.get(i), '=')) {
                throw new IllegalArgumentException(file + " line " + (i + 1) + ": a case begins"
                        + " with a line of `=`");
            }
            i++;
            String name = lines.get(i).strip();
            i++;
            boolean refused = false;
            while (lines.get(i).startsWith(":")) {
                if (!lines.get(i).strip().equals(":error")) {
                    throw new IllegalArgumentException(file + " line " + (i + 1)
                            + ": an attribute this corpus does not use: " + lines.get(i));
                }
                refused = true;
                i++;
            }
            if (!isRule(lines.get(i), '=')) {
                throw new IllegalArgumentException(file + " line " + (i + 1) + ": the name of `"
                        + name + "` is not closed by a line of `=`");
            }
            i++;
            int sourceStart = i;
            while (i < lines.size() && !isRule(lines.get(i), '-')) {
                i++;
            }
            if (i >= lines.size()) {
                throw new IllegalArgumentException(file + ": `" + name + "` has no line of `-`");
            }
            String source = withoutBlankEnds(lines.subList(sourceStart, i));
            i++;
            int treeStart = i;
            while (i < lines.size() && !isRule(lines.get(i), '=')) {
                i++;
            }
            String tree = String.join("\n", lines.subList(treeStart, i)).strip();
            if (refused != tree.isEmpty()) {
                throw new IllegalArgumentException(file + ": `" + name + "` "
                        + (refused ? "is refused and still writes a tree"
                                : "writes no tree and is not marked :error"));
            }
            out.add(new Case(file, name, source,
                    refused ? new Refused() : new Accepted(ContractTree.parse(tree))));
        }
        return out;
    }

    private static boolean isRule(String line, char c) {
        String stripped = line.strip();
        return stripped.length() >= 3 && stripped.chars().allMatch(each -> each == c);
    }

    private static String withoutBlankEnds(List<String> lines) {
        int from = 0;
        int to = lines.size();
        while (from < to && lines.get(from).isEmpty()) {
            from++;
        }
        while (to > from && lines.get(to - 1).isEmpty()) {
            to--;
        }
        return String.join("\n", lines.subList(from, to));
    }
}
