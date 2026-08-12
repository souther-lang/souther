package souther.compiler;

import java.util.ArrayList;
import java.util.List;

/**
 * What this command line takes, written out.
 *
 * <p>Nothing here knows a command from another one. What to write about {@code compile} is read off
 * {@link CliCommand} and {@link CliOption} exactly as it is read off them for every other command,
 * so a command or an option added to those tables is written out without this class being told. A
 * branch on a particular command appearing here would mean the tables had stopped carrying
 * something a reader is shown, and that thing would then be documented in a renderer.
 *
 * <p>This used to be one string held against the tables by a test, which is what it takes to keep
 * two statements of one fact agreeing. It had drifted anyway: {@code mcp} was written as an option
 * of {@code api}, and {@code --behavior} was documented under {@code examples} alone though
 * {@code run} takes it too.
 */
final class Usage {

    /** How wide a written line runs, the formatter's own width. */
    private static final int WIDTH = 100;

    /** What stands between the widest thing in a column and what is written against it. */
    private static final int GAP = 2;

    private static final String INDENT = "  ";

    /** What the command line takes: every command it has, and how to ask about one of them. */
    static String all() {
        List<String> lines = new ArrayList<>();
        lines.add("usage: souther <command> [options] [args]");
        lines.add("");
        lines.add("commands:");
        int column = column(java.util.Arrays.stream(CliCommand.values())
                .map(CliCommand::spelling).toList());
        for (CliCommand command : CliCommand.values()) {
            lines.addAll(entry(command.spelling(), command.summary(), column));
        }
        lines.add("");
        lines.add("`souther help <command>` writes what one command takes,"
                + " and `souther doc cli/commands` writes the whole of it.");
        return String.join(System.lineSeparator(), lines);
    }

    /**
     * What one command takes: how it is written, what it is for, and every option it has.
     *
     * <p>Its options are the ones {@link CliOption} says are this command's, in the order that
     * table writes them — the command's own first and the ones every command shares last. Not the
     * ones written under its heading somewhere, which is what left {@code run} documented without
     * the {@code --behavior} it takes.
     */
    static String of(CliCommand command) {
        List<String> lines = new ArrayList<>();
        lines.add(("usage: souther " + command.spelling() + " [options] "
                + command.operands()).stripTrailing());
        lines.add(INDENT + command.summary());
        // Never none of them: `--help` is every command's, so a command that takes nothing else
        // still has this section, which is the one a reader who got here by asking is reading.
        List<CliOption> options = optionsOf(command);
        lines.add("");
        lines.add("options:");
        int column = column(options.stream().map(Usage::written).toList());
        for (CliOption option : options) {
            lines.addAll(entry(written(option), command.describe(option), column));
        }
        return String.join(System.lineSeparator(), lines);
    }

    /** The options this command takes, in the order the table writes them. */
    private static List<CliOption> optionsOf(CliCommand command) {
        List<CliOption> options = new ArrayList<>();
        for (CliOption option : CliOption.values()) {
            if (option.ownedBy(command.spelling())) {
                options.add(option);
            }
        }
        return options;
    }

    /** How an option is written where it is listed: every spelling it has, and its value. */
    private static String written(CliOption option) {
        String spelt = String.join(", ", option.spellings());
        return option.takesAValue() ? spelt + " " + option.valueSpelling() : spelt;
    }

    /** Where the second column begins: past the widest thing in the first, and the gap. */
    private static int column(List<String> first) {
        int widest = 0;
        for (String written : first) {
            widest = Math.max(widest, written.length());
        }
        return INDENT.length() + widest + GAP;
    }

    /**
     * One two-column line, and the lines its description runs onto.
     *
     * <p>A description too long for what is left of the width is carried on at the column it began
     * at, rather than being written out past the edge or cut. What runs on is indented under the
     * description and never under the name, so a line that runs on cannot be read as another
     * option.
     */
    private static List<String> entry(String name, String description, int column) {
        List<String> lines = new ArrayList<>();
        String pad = " ".repeat(column);
        StringBuilder line = new StringBuilder(INDENT).append(name);
        while (line.length() < column) {
            line.append(' ');
        }
        for (String word : description.split(" ")) {
            if (line.length() > column && line.length() + 1 + word.length() > WIDTH) {
                lines.add(line.toString());
                line = new StringBuilder(pad);
            } else if (line.length() > column) {
                line.append(' ');
            }
            line.append(word);
        }
        lines.add(line.toString());
        return lines;
    }

    private Usage() {}
}
