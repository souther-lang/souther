package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Who may ask after the inputs a reading kept is taken again without regard to unless it asked
 * after them ({@code Pullback#kept}).
 *
 * <p>A reading kept says which of {@code sideAsWritten}, {@code answering}, {@code countsMet} and
 * {@code telling} it asked after, and is taken where the others stand otherwise. What it says is
 * what went through the accessor of each, so an asking that did not is an input the reading
 * depends on and is not told, and the reading is taken where it would not be the same reading.
 * What is not an asking is the declaration, setting one, saving it to put it back, and the
 * accessor itself.
 */
class OnlyTheAccessorsAskAfterWhatAReadingMayLeaveUnconsultedTest {

    private static final List<String> INPUTS =
            List.of("sideAsWritten", "answering", "countsMet", "telling");

    /** The lines of the file that are code and say the name of an input: not what a comment says. */
    private static List<String> linesNaming(String name) throws IOException {
        Pattern named = Pattern.compile("\\b" + name + "\\b(?!\\()");
        return Files.readAllLines(Path.of("src/main/java/souther/compiler/partition/Pullback.java"))
                .stream()
                .filter(line -> !line.strip().startsWith("*") && !line.strip().startsWith("//")
                        && !line.strip().startsWith("/*"))
                .filter(line -> named.matcher(line).find())
                .toList();
    }

    private static boolean notAnAsking(String name, String line) {
        String code = line.strip();
        return code.matches("private [^=(]*\\b" + name + ";")
                || code.matches(name + " = [^=].*")
                || code.matches(".* outer\\w* = " + name + ";")
                || code.equals("return " + name + ";")
                || code.contains("placeOfTheInput(\"" + name + "\")")
                // A local that is a different thing and is named alike.
                || code.contains("AnOperationApplied " + name + " =")
                || code.contains(name + " == null ? null : " + name + ".operation()");
    }

    @Test
    void noPlaceAsksAfterAnInputWithoutTellingIt() throws IOException {
        Set<String> found = new TreeSet<>();
        for (String name : INPUTS) {
            for (String line : linesNaming(name)) {
                if (!notAnAsking(name, line)) {
                    found.add(name + ": " + line.strip());
                }
            }
        }

        assertEquals(Set.of(), found);
    }

    /**
     * What a list or a map that is written into holds is asked by its own accessor
     * ({@code answeringContent()}, {@code countsMetContent()}), which tells the reading it was
     * asked, so that a reading kept is taken only where it holds what it did. The accessor of
     * whether it is there is asked only that, or to add to it.
     */
    @Test
    void whatAWrittenIntoInputHoldsIsAskedOnlyThroughTheAccessorOfWhatItHolds()
            throws IOException {
        Set<String> found = new TreeSet<>();
        for (String name : List.of("answering", "countsMet")) {
            Pattern presence = Pattern.compile("\\b" + name + "\\(\\)");
            for (String line : Files.readAllLines(Path.of(
                    "src/main/java/souther/compiler/partition/Pullback.java"))) {
                String code = line.strip();
                if (code.startsWith("*") || code.startsWith("//") || code.startsWith("/*")
                        || !presence.matcher(code).find()) {
                    continue;
                }
                boolean onlyWhetherItIsThere = code.contains(name + "() == null")
                        || code.contains(name + "() != null")
                        || code.contains(name + "().add(") || code.contains(name + "().addAll(")
                        || code.contains(name + "().computeIfAbsent(")
                        || code.matches(".* " + name + "\\(\\) \\{");
                if (!onlyWhetherItIsThere) {
                    found.add(name + ": " + code);
                }
            }
        }

        assertEquals(Set.of(), found);
    }

    @Test
    void theInputsAreFoundWhereTheyAreSet() throws IOException {
        for (String name : INPUTS) {
            assertEquals(true, linesNaming(name).stream()
                            .anyMatch(line -> line.strip().matches("private [^=(]*\\b" + name + ";")),
                    name + " is declared in Pullback");
        }
    }
}
