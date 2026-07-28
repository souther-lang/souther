package souther.compiler.diag;

/**
 * A secondary source region with a note. Used when one error points at more than one place — the
 * left behavior's output and the right behavior's input of a failed composition, or the two
 * branches of an {@code if} that disagree. {@code labelKey} is a catalog key (its prose follows the
 * locale); {@code labelArgs} fill its placeholders.
 */
public record LabeledRegion(Region region, String labelKey, Object[] labelArgs) {

    /** What makes two labels the same label. A record compares an array component by identity, and
     * {@code labelArgs} is one. */
    public record Of(Region region, String labelKey, java.util.List<Object> labelArgs) {}

    public Of identity() {
        return new Of(region, labelKey,
                labelArgs == null ? java.util.List.of() : java.util.Arrays.asList(labelArgs));
    }
}
