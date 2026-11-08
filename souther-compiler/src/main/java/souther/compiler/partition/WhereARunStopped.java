package souther.compiler.partition;

import souther.compiler.execute.RunStop;
import souther.compiler.source.SourceId;

import java.util.Objects;
import java.util.Optional;

/**
 * Where a composed row's run stopped without answering, with the source its place is written in.
 *
 * <p>What the generated code and the runtime said, and which of this compilation's sources the
 * module they named is written in — asked of the compilation where the run is read, since the code
 * that stopped knows a module and not a source. None where the stop names no module, or where no
 * source of this compilation declares the one it names.
 *
 * @param stop   what the run said of where it stopped
 * @param source the source the place is written in, where this compilation has it
 */
public record WhereARunStopped(RunStop stop, Optional<SourceId> source) {

    public WhereARunStopped {
        Objects.requireNonNull(stop, "a run stopped somewhere");
        Objects.requireNonNull(source, "a place is in one of these sources or in none");
    }
}
