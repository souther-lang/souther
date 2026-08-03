package souther.compiler.partition;

/**
 * What names an axis across a report: the behavior it is an input of, and where in that input it sits.
 *
 * <p>A value rather than the axis itself, so that an obligation or a coverage row can say which axis
 * it is about without holding the classes and their classifiers.
 */
public record AxisId(String behavior, String path) {

    public static AxisId of(String behavior, TermPath path) {
        return new AxisId(behavior, path.toString());
    }

    @Override
    public String toString() {
        return behavior + "/" + path;
    }
}
