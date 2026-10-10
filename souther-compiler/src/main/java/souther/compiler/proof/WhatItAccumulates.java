package souther.compiler.proof;

import souther.compiler.core.TheWalk;
import souther.compiler.semantics.Accumulation;
import souther.compiler.types.BinOp;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Whether an operation the library writes answers what a container holds accumulated, proved
 * against its body.
 *
 * <p>An accumulation is a walk and says which: over the container's elements from the first,
 * started from the identity, each step combining what is carried with the element it is handed.
 * The body shows it by being that walk — one answer, the walk itself, and a step that is the
 * combination and nothing else.
 */
public final class WhatItAccumulates {

    private final Library library;
    private final Set<ValueName.Stdlib.Operation> readThrough;

    /**
     * @param readThrough the operations whose bodies are read where they are called, as the
     *                    proofs of what the library's operations come to read them
     */
    public WhatItAccumulates(Library library, Set<ValueName.Stdlib.Operation> readThrough) {
        this.library = library;
        this.readThrough = Set.copyOf(readThrough);
    }

    /** Whether {@code operation}'s body is the walk over its argument at {@code container} that
     *  {@code how} says. */
    public LibraryProver.Outcome prove(ValueName.Stdlib.Operation operation, int container,
                                       Accumulation how) {
        Reading reading = new Reading(library, readThrough);
        try {
            List<Value> params = new ArrayList<>();
            for (int at = 0; at < library.takes(operation).size(); at++) {
                params.add(new Value.Argument(at));
            }
            List<Reading.Case> cases = reading.cases(reading.bodyOf(operation),
                    new Reading.Frame(params, Map.of()));
            TheWalk walk = library.stdlib().walk();
            if (cases.size() != 1 || !(cases.getFirst().is() instanceof Value.Made(
                    ValueName.Stdlib.Operation walks, List<Value> args))
                    || !walks.equals(walk.operation())
                    || !(args.get(walk.index()) instanceof Value.Whole(long from)) || from != 0
                    || !args.get(walk.container()).equals(new Value.Argument(container))
                    || !args.get(walk.seed()).equals(identity(how.identity()))) {
                return notThat();
            }
            Value carried = new Value.Fresh(1, "what the walk carries");
            Value next = new Value.Fresh(3, "the element the walk is handed next");
            List<Value> handed = new ArrayList<>(List.of(next, next));
            handed.set(walk.accumulator(), carried);
            handed.set(walk.element(), next);
            List<Reading.Case> steps = reading.applied(args.get(walk.step()), handed);
            if (steps.size() != 1
                    || !steps.getFirst().is().equals(combined(how.combine(), carried, next))) {
                return notThat();
            }
            return new LibraryProver.Outcome.Proved(
                    new Proof.ByTheBody(operation, reading.used()));
        } catch (Reading.Stopped stopped) {
            return LibraryProver.stoppedAt(stopped);
        }
    }

    private static LibraryProver.Outcome notThat() {
        return new LibraryProver.Outcome.Open(
                new Unproved.DoesNotFollow(Unproved.Obligation.THE_STATEMENT));
    }

    /** The value {@code identity} is, as a body writes it. */
    private static Value identity(Accumulation.Identity identity) {
        return switch (identity) {
            case ZERO -> new Value.Whole(0);
            case ONE -> new Value.Whole(1);
            case EMPTY -> new Value.Listed(List.of());
        };
    }

    /** What a step combining {@code carried} with {@code next} as {@code combine} says comes to. */
    private static Value combined(Accumulation.Combine combine, Value carried, Value next) {
        return switch (combine) {
            case ADD -> new Value.Arithmetic(BinOp.ADD, carried, next);
            case MULTIPLY -> new Value.Arithmetic(BinOp.MUL, carried, next);
            case APPEND -> new Value.Joined(carried, next);
        };
    }
}
