package souther.compiler.diag;

/**
 * A secondary source region with a note. Used when one error points at more than one place — the
 * left behavior's output and the right behavior's input of a failed composition, or the two
 * branches of an {@code if} that disagree. {@code labelKey} is a catalog key (its prose follows the
 * locale); {@code labelArgs} fill its placeholders.
 *
 * <p>{@code sourceId} names the source this region is in, and is null for the ordinary case where
 * that is the diagnostic's own. A problem written in two files — a stand-in in one and the row it
 * contradicts in another — names the second, so the renderer quotes the right text rather than the
 * line that happens to sit at that number in the first. Read it through
 * {@link #sourceIdOr(String)}: a resolver is asked about a source that is named, never about null.
 */
public record LabeledRegion(Region region, String sourceId, String labelKey, Object[] labelArgs) {

    /** The source this region is in, inheriting {@code diagnosticSourceId} when it names none. */
    public String sourceIdOr(String diagnosticSourceId) {
        return sourceId == null ? diagnosticSourceId : sourceId;
    }

    /** What makes two labels the same label. A record compares an array component by identity, and
     * {@code labelArgs} is one. */
    public record Of(Region region, String sourceId, String labelKey,
                     java.util.List<Object> labelArgs) {}

    public Of identity() {
        return new Of(region, sourceId, labelKey,
                labelArgs == null ? java.util.List.of() : java.util.Arrays.asList(labelArgs));
    }
}
