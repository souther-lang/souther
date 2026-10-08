package souther.compiler.partition;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.Comparison;
import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.ScopeStep;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.meaning.MeaningsOfABody;
import souther.compiler.semantics.ConditionJoin;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.ModelOccurrence;

import java.util.Optional;
import java.util.function.Supplier;

/**
 * What each condition of a body states, read off the tree where the language's operations stand
 * and filed under the construct of the model it is asked at ({@link MeaningsOfABody}).
 *
 * <p>Three places a truth is asked, because those are the three a reader of the tree that runs
 * takes one in at: a fork's condition, the left operand of a short-circuit, and a comparison whose
 * outcome a run records. Each is read where it stands — under the bindings, arms and closures
 * above it — which is the one reading of what it states ({@link Pullback}).
 */
public final class MeaningsOfABodyReading {

    private final Supplier<InputReading> reading;
    private final Symbols symbols;
    private final DeclarationNewtypes newtypes;
    private InputReading read;
    private final MeaningsOfABody.Filing filed = new MeaningsOfABody.Filing();

    private MeaningsOfABodyReading(Supplier<InputReading> reading, Symbols symbols,
                                   DeclarationNewtypes newtypes) {
        this.reading = reading;
        this.symbols = symbols;
        this.newtypes = newtypes;
    }

    /**
     * What each condition of {@code analysis} states, its names read as {@code reads} has them.
     *
     * <p>The input is read where a condition is met and not before: a body with nothing to read
     * the meaning of asks nothing of the rules its input is read by, and an answer depending on
     * them would be worked out again whenever they are.
     */
    public static MeaningsOfABody of(AnalysisBody analysis, Supplier<InputReading> read,
                                     InputReads reads, Symbols symbols,
                                     DeclarationNewtypes newtypes) {
        MeaningsOfABodyReading reading = new MeaningsOfABodyReading(read, symbols, newtypes);
        reading.walk(analysis.core(), reads);
        return reading.filed.filed();
    }

    private InputReading read() {
        if (read == null) {
            read = reading.get();
        }
        return read;
    }

    private void walk(Core e, InputReads reads) {
        switch (Core.withoutStanding(e)) {
            case Core.If iff -> asked(iff.place().occurrence(), MeaningsOfABody.Part.CONDITION,
                    iff.cond(), reads);
            case Core.Binary binary when ConditionJoin.of(binary.op()).isPresent() ->
                    asked(binary.occurrence(), MeaningsOfABody.Part.LEFT, binary.left(), reads);
            case Core.Binary binary when Comparison.of(binary).isPresent() ->
                    asked(binary.occurrence(), MeaningsOfABody.Part.ITSELF, binary, reads);
            default -> { }
        }
        ScopeStep.forEachChild(e, (child, step) -> walk(child,
                reads.entering(step, symbols, newtypes)));
    }

    /** What {@code truth} states, filed at {@code part} of the construct {@code at} is one of. */
    private void asked(ConstructOccurrence at, MeaningsOfABody.Part part, Core truth,
                       InputReads reads) {
        Optional<ModelOccurrence> construct = ModelOccurrence.statedAt(at);
        if (construct.isEmpty()) {
            return;
        }
        MeaningsOfABody.Site site = new MeaningsOfABody.Site(construct.get(), part);
        filed.met(site, Pullback.ofATruth(truth, reads, read(), construct).meaning());
    }
}
