package souther.compiler.reading;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.inputs.AnInputRead;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.meaning.MeaningsOfABody;
import souther.compiler.partition.MeaningsOfABodyReading;
import souther.compiler.revision.RevisionKnowledge;
import souther.compiler.revision.RevisionWork;

import java.util.Objects;

/**
 * What each condition of a body states against one input, as work settled by the body, the input
 * and the source its rules are read from.
 *
 * <p>Where a run of the body gets to and what the run meets each need it. Walked by each for itself,
 * every truth in the body is read twice, of one reading of one input. Settled here, the first of
 * them reads the body and the other is lent that reading.
 *
 * <p>Everything the walk reads is worked out here from those three. A caller handing in the names
 * the body is read with, or the reading of the input, would be handing in part of what the answer
 * is settled by without it being part of which work this is: two askings with the same three and
 * different names would be one piece of work with the first asking's answer.
 *
 * <p>The body by identity: the readers are handed the tree the check made, and comparing it by what
 * it holds would walk it to say so. The source by its origin, as {@link AnInputRead} is; the source
 * is carried to do the work with and is no part of which work this is.
 */
public final class WhatABodyStates implements RevisionWork<MeaningsOfABody> {

    private final AnalysisBody analysis;

    private final InputDomain input;

    private final RuleReadingSource.Origin origin;

    private final RuleReadingSource source;

    private WhatABodyStates(AnalysisBody analysis, InputDomain input,
                            RuleReadingSource source) {
        this.analysis = Objects.requireNonNull(analysis, "a body is what is read");
        this.input = Objects.requireNonNull(input, "an input is what it is read against");
        this.origin = source.origin();
        this.source = source;
    }

    /** What the conditions of {@code analysis} state against {@code input}, as {@code revision}
     *  has it: worked out for the first asking and lent to the rest. */
    public static MeaningsOfABody of(AnalysisBody analysis, InputDomain input, RuleReadingSource source,
                              RevisionKnowledge revision) {
        return revision.settled(new WhatABodyStates(analysis, input, source));
    }

    @Override
    public MeaningsOfABody workedOut(RevisionKnowledge revision) {
        // The input is read where a condition is met and not before: a body with nothing to read
        // the meaning of asks nothing of the rules its input is read by.
        return MeaningsOfABodyReading.of(analysis,
                () -> revision.settled(new AnInputRead(input, source)),
                InputReads.ofParametersWhereCallsStand(input.parameterReads(),
                        input.declared(source), ElementBindings.of(analysis, source.newtypes()),
                        input.dependencies()),
                source.symbols(), source.newtypes());
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof WhatABodyStates it && analysis == it.analysis
                && input.equals(it.input) && origin.equals(it.origin);
    }

    @Override
    public int hashCode() {
        return Objects.hash(System.identityHashCode(analysis), input, origin);
    }

    @Override
    public String toString() {
        return "WhatABodyStates[" + input.parameters() + "]";
    }
}
