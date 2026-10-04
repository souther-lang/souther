package souther.compiler.query;

import souther.compiler.check.BoundaryInput;
import souther.compiler.execute.BoundaryValues;
import souther.compiler.execute.BoundaryValues.Built;
import souther.compiler.execute.ProgramExecution;
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.types.FixtureReferenceOrigin;
import souther.compiler.types.Type;

import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

/**
 * A module's boundary asked about values as a row writes them, each answered once.
 *
 * <p>A search asks about one candidate at every point of a border it is tried at and under every
 * way of standing the dependencies in, and the decoder says the same thing each time. Whether the
 * value stands at the point is the other half of that question and is asked of what comes back
 * here, every time; it is not this one's to keep.
 *
 * <p>What is kept is what came back: a value, or a refusal, both of which are what the decoder says
 * about the fixture. What was thrown is not kept. A runtime that would not link and an evaluation
 * that ran out of what it may spend are about this compile and this run, and the next asking is
 * entitled to find out again.
 *
 * <p>Kept by the text a row writes, and not by the tree. The tree is not what the question is about:
 * two composed occurrences of one named value carry different reference origins in their trees
 * ({@link FixtureReferenceOrigin}), while a row writes the same value for both and the decoder
 * answers the same about both. The text is enough because both forms of a fixture are written from
 * one answer about what its names reach, and the names this module writes reach one thing each, so
 * one text at one position is one value. Two texts for one value are asked about twice, which costs a
 * build and says nothing wrong.
 *
 * <p>Here and not behind {@link ProgramExecution}. What an execution is handed is the tree it builds
 * from; the text is how this compiler's generator writes a row, and an execution has no use for it
 * beyond being told what to keep.
 *
 * <p>Kept for as long as {@code source} is, because {@code source} is what the answers are about.
 * Shared between two of them, an answer worked out against one module's classes would be handed back
 * about the other's.
 */
public final class FixturesAtTheBoundary {

    private record Asked(BoundaryInput at, String written) {}

    private record AskedAlone(Type type, String written) {}

    private final BoundaryValues source;

    private final Map<Asked, Built> answered = new ConcurrentHashMap<>();

    private final Map<AskedAlone, BoundaryValues.OnItsOwn> answeredAlone =
            new ConcurrentHashMap<>();

    private FixturesAtTheBoundary(BoundaryValues source) {
        this.source = source;
    }

    static FixturesAtTheBoundary remembering(BoundaryValues source) {
        return new FixturesAtTheBoundary(source);
    }

    /**
     * What building {@code fixture} at {@code at} came to, built the first time it is asked.
     *
     * <p>Throws what {@code source} throws, and keeps none of it.
     */
    public Built build(BoundaryInput at, FixtureTemplate fixture) {
        Asked asked = new Asked(at, fixture.text());
        Built had = answered.get(asked);
        if (had != null) {
            return had;
        }
        // Built outside the map rather than inside computeIfAbsent: a decoder can run for a while,
        // and the map would hold everything hashed beside this fixture until it finished. Two
        // threads that race build the same answer, and the first one kept is the one both return.
        Built made = source.build(at, fixture.value());
        Built kept = answered.putIfAbsent(asked, made);
        return kept == null ? made : kept;
    }

    /**
     * What building {@code fixture} as {@code type} on its own came to, built the first time it is
     * asked.
     *
     * <p>Kept by the type and the text for the reason {@link #build} keeps by the position and the
     * text. A search asks it of every value in an assignment before composing that assignment, the
     * first one included, and the same few values stand at the same few types across every search
     * of a module.
     *
     * <p>Throws what {@code source} throws, and keeps none of it.
     */
    public BoundaryValues.OnItsOwn buildAlone(Type type, FixtureTemplate fixture) {
        AskedAlone asked = new AskedAlone(type, fixture.text());
        BoundaryValues.OnItsOwn had = answeredAlone.get(asked);
        if (had != null) {
            return had;
        }
        BoundaryValues.OnItsOwn made = source.buildAlone(type, fixture.value());
        BoundaryValues.OnItsOwn kept = answeredAlone.putIfAbsent(asked, made);
        return kept == null ? made : kept;
    }
}
