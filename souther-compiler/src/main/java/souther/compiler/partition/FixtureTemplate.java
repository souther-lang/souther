package souther.compiler.partition;

/**
 * A value written the way a row writes it — the text a generated {@code example} row would carry at
 * one position, such as {@code Amount(0)}, {@code None}, or {@code Overseas}.
 *
 * <p>Text rather than a built value because what it is for is being printed into a row for a person
 * to read and complete. Whether it can be built is settled by building it, which is the generator's
 * job and not this one's.
 */
public record FixtureTemplate(String text) {

    public FixtureTemplate {
        if (text == null || text.isBlank()) {
            throw new IllegalArgumentException("a fixture template is written text");
        }
    }
}
