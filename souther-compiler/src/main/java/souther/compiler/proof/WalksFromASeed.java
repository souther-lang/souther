package souther.compiler.proof;

import souther.compiler.core.TheWalk;
import souther.compiler.semantics.Combinator;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.BindingId;
import souther.compiler.types.ValueName;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Which operations the library defines are a walk from a seed through their closure, answering the
 * value the walk ends with — and where the seed and what is carried are — read off their bodies.
 *
 * <p>The walk itself is one ({@link TheWalk}). An operation is another where its body is a call of
 * one, from the first element, that answers what that call answers, starting from one of the
 * operation's own arguments, with a step that is the operation's closure or that hands the closure
 * on what is carried as it is and answers what the closure answers. {@code Set.fold} hands its
 * closure over as the step; {@code List.foldRight} and {@code Map.fold} hand what is carried on in
 * a place of their own choosing, and that place is what is read.
 *
 * <p>What a walk licenses is what {@link TheWalk} says of the walk and nothing else: its answer is
 * the seed, or the step applied to an earlier answer and an element. That is all a reader of these
 * may assume.
 */
public final class WalksFromASeed {

    /** Where a walk's seed and what it carries are: the argument holding the seed, and the
     *  closure's parameter the value carried so far arrives on. */
    public record Walk(int seedArg, int accumulatorParam) {}

    private WalksFromASeed() {}

    /**
     * The walks among {@code library}'s operations, given what each hands its closure.
     *
     * @param applied what each operation hands its closure, as {@link AppliedClosures} reads it
     */
    public static Map<ValueName.Stdlib.Operation, Walk> of(
            Stdlib library, Map<ValueName.Stdlib.Operation, Combinator> applied) {
        TheWalk walk = library.walk();
        Map<ValueName.Stdlib.Operation, Walk> walks = new LinkedHashMap<>();
        walks.put(walk.operation(), new Walk(walk.seed(), walk.accumulator()));
        library.helpers().forEach((operation, declaration) -> {
            if (walks.containsKey(operation) || applied.get(operation) == null) {
                return;
            }
            Walk read = readOff(LibraryTerms.of(library, declaration), walks, applied,
                    applied.get(operation).closureArg());
            if (read != null) {
                walks.put(operation, read);
            }
        });
        library.rewrites().forEach((sugar, rewrite) -> {
            Walk target = walks.get(rewrite.target());
            if (target != null && target.seedArg() < rewrite.keptArgs()
                    && applied.containsKey(sugar)) {
                walks.put(sugar, target);
            }
        });
        return Map.copyOf(walks);
    }

    /** The walk {@code body} is, where it answers a call of one that takes its seed from the
     *  operation's own arguments and its step from the closure at {@code closure}. */
    private static Walk readOff(LibraryTerm body, Map<ValueName.Stdlib.Operation, Walk> walks,
                                Map<ValueName.Stdlib.Operation, Combinator> applied, int closure) {
        if (!(body instanceof LibraryTerm.Call call)) {
            return null;
        }
        Walk walk = walks.get(call.operation());
        Combinator steps = applied.get(call.operation());
        if (walk == null || steps == null || walk.seedArg() >= call.args().size()
                || steps.closureArg() >= call.args().size()
                || !(call.args().get(walk.seedArg()) instanceof LibraryTerm.Parameter(int seed))
                || !fromTheFirst(steps, call)) {
            return null;
        }
        LibraryTerm step = call.args().get(steps.closureArg());
        if (step instanceof LibraryTerm.Parameter(int position) && position == closure) {
            return new Walk(seed, walk.accumulatorParam());
        }
        if (!(step instanceof LibraryTerm.Closure written)
                || walk.accumulatorParam() >= written.params().size()) {
            return null;
        }
        BindingId carried = written.params().get(walk.accumulatorParam());
        LibraryTerm answers = written.body();
        while (answers instanceof LibraryTerm.Let let) {
            answers = let.body();
        }
        if (!(answers instanceof LibraryTerm.Applied(LibraryTerm.Parameter(int function),
                List<LibraryTerm> args)) || function != closure) {
            return null;
        }
        int at = -1;
        for (int i = 0; i < args.size(); i++) {
            if (args.get(i) instanceof LibraryTerm.Bound(BindingId binding)
                    && binding.equals(carried)) {
                if (at >= 0) {
                    return null;   // what is carried is handed on twice, and is neither the one
                }
                at = i;
            }
        }
        return at < 0 ? null : new Walk(seed, at);
    }

    private static boolean fromTheFirst(Combinator steps, LibraryTerm.Call call) {
        return steps.startsFrom() == Combinator.FROM_THE_FIRST
                || (steps.startsFrom() < call.args().size()
                && call.args().get(steps.startsFrom()) instanceof LibraryTerm.WholeNumber(long n)
                && n == 0);
    }
}
