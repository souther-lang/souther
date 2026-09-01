package souther.compiler.partition;

import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * A measurement over axes a test wrote, rather than over a reading of any declaration.
 *
 * <p>A subject is a reading of an input and the measurement made against it, and the measurement is
 * where the model divides the input. A test about the search itself has no model to divide — it
 * writes the two or three classes the search is to walk — so what it needs is a measurement holding
 * exactly those axes and answering nothing else.
 *
 * <p>Here rather than in the production factory. What a caller may hand over is the measurement, so
 * a test that wants one writes one; a second production entry taking a bare list of axes would be a
 * way for anything to assemble a subject from classes it chose, which is what one place making them
 * exists to stop.
 *
 * <p>The positions are written the way {@link PositionAccount#at} means them: outside a reading, so
 * they carry no residue and answer for nothing. What a position here is declared to be is written
 * down because a position has to be something and is read by nothing that reaches this — the
 * measures are what a caller of this is about, and a test asking what a position's reading came to
 * wants a real reading rather than one of these.
 */
public final class AxesATestWrote {

    private AxesATestWrote() {}

    /** A measurement of {@code behavior} that divides its positions by exactly {@code axes}. */
    public static Partitions.Partitioning asAMeasurement(String behavior, List<Axis> axes) {
        List<PositionMeasurements> measurements = new ArrayList<>(axes.size());
        for (Axis axis : axes) {
            measurements.add(new PositionMeasurements(
                    PositionAccount.at(behavior, axis.path(), Type.INT),
                    List.of(axis), new BodyCutInspection.Evidence()));
        }
        // Closed, because nothing here was left unread: the axes are the whole of what this
        // divides. Asked of the same fold a reading's own closure comes from, so that a test does
        // not write down a second answer to what a closed measure is.
        MeasureClosure.Both closed = MeasureClosure.of(
                measurements.stream().map(PositionMeasurements::position).toList(),
                List.of(), List.of(), new LinesRead());
        return new Partitions.Partitioning(measurements, List.of(), Set.of(), List.of(), List.of(),
                List.of(), Map.of(), ReachingCuts.NONE,
                closed.partition(), closed.border(), null);
    }
}
