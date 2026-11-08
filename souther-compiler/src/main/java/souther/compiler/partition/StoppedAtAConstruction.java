package souther.compiler.partition;

import souther.compiler.execute.RefusedConstruction;
import souther.compiler.source.SourceId;

import java.util.Objects;
import java.util.Optional;

/**
 * A construction a composed row's run stopped at, with the source its place is in.
 *
 * <p>What the generated code said, and which of this compilation's sources the module it named is
 * written in — asked of the compilation where the run is read, since the code that stopped knows a
 * module and not a source. None where no source of this compilation declares that module.
 *
 * @param refused what the generated code said of it
 * @param source  the source the construction is written in, where this compilation has it
 */
public record StoppedAtAConstruction(RefusedConstruction refused, Optional<SourceId> source) {

    public StoppedAtAConstruction {
        Objects.requireNonNull(refused, "a stop at a construction is some construction refused");
        Objects.requireNonNull(source, "a construction is in one of these sources or in none");
    }
}
