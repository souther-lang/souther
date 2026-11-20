package souther.compiler;

/**
 * Whether a report in English says that something it measured is not read, by the finding that
 * says so: a line the finding's headline opens. The words standing anywhere else, in what another
 * finding says or in the reason a finding gives, are that finding's own words and no finding that
 * something is not read.
 */
public final class NotRead {

    /** What opens the finding, after the mark every finding is set out with. */
    private static final String HEADLINE = "· not read:";

    private NotRead() {
    }

    /** Whether {@code line} is the finding that something is not read. */
    public static boolean isOne(String line) {
        return line.strip().startsWith(HEADLINE);
    }

    /** Whether {@code report} says of anything that it is not read. */
    public static boolean in(String report) {
        return report.lines().anyMatch(NotRead::isOne);
    }
}
