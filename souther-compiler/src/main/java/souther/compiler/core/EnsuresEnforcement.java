package souther.compiler.core;

import souther.compiler.abort.AbortKind;
import souther.compiler.abort.AbortSet;
import souther.compiler.types.ValueName;

import java.util.Map;

/**
 * What is being done about a behavior's {@code ensures}, answered once for the whole compilation.
 *
 * <p>Here rather than beside the check, because where a clause is checked is a decision the
 * language made and an output other than this compiler's own reads it. What rides it is the
 * executable reading of the declaration ({@link Contract}), which is the same value the emitter
 * runs and the same one a checked program is given.
 *
 * <p>One value rather than a pair of questions. Asked as "does the callee check" and "does a
 * crossing check", the two are complements in arithmetic and independent in the program: four
 * combinations can be written where three answers exist, and the two that should be unreachable are
 * the ones that matter. Both false is a clause nothing checks, which is the failure this whole
 * mechanism exists to prevent and which nothing would report. Both true is a clause checked twice,
 * which is silent and costs a run on every call. They would be read at the same place, too — a
 * pipeline stage's application is where a bodied stage's own check already runs and where an
 * injected stage's crossing check goes.
 *
 * <p>The module declaring a behavior decides, and its answer is the answer wherever the behavior is
 * called. Both facts it rests on are the behavior's own — what it declares, and whether Java supplies
 * its body — so a caller in another module has nothing to decide differently: a body checks its own
 * answer for every caller, and an answer Java supplies enters the program at every call, whoever
 * makes it. What a caller reads of it is the callee's projection
 * ({@code LinkageProjection.Behavior#checkedWhereCalled}), which an artifact records, so a caller
 * built against a module whose clause has since moved is told so when it is linked again.
 */
public sealed interface EnsuresEnforcement {

    /**
     * The module that declares the behavior checks it where the behavior answers.
     *
     * <p>Its body is here, so this is the one place every application goes through — a Souther
     * caller, a Java caller, a pipeline stage — and a caller emits nothing.
     */
    record AtTheCallee(Contract contract) implements EnsuresEnforcement {

        public AtTheCallee {
            if (contract == null) {
                throw new IllegalArgumentException("a check is of something a behavior declared");
            }
        }
    }

    /**
     * The answer arrives from outside, so every crossing into generated code checks it, in whichever
     * module the crossing is.
     *
     * <p>An injected behavior's {@code apply} is supplied by the Java implementation (ADR-0056), so
     * there is no body here to check in. The line is the one the Decoder draws for an outside value:
     * where an answer enters the domain.
     *
     * <p>This says where a check goes, not how many go anywhere. A behavior only the application's
     * own Java calls has no crossing in this compilation and gets no check emitted — a count of
     * crossings, and not an answer of its own.
     */
    record AtEachCrossing(Contract contract) implements EnsuresEnforcement {

        public AtEachCrossing {
            if (contract == null) {
                throw new IllegalArgumentException("a check is of something a behavior declared");
            }
        }
    }

    /** The behavior declares no clause, so there is nothing to run. A conclusion, reached by reading
     *  what the behavior declared. */
    record NoContract() implements EnsuresEnforcement {

        /** The one of these there is. It holds nothing, so a second instance would be a second name
         *  for one answer. */
        public static final NoContract INSTANCE = new NoContract();
    }

    /**
     * What is checked, or null where nothing is.
     *
     * <p>The contract rides the answer rather than being looked up beside it. An emitter needs both
     * — where the check goes and what it says — and handed them apart it would hold a case saying
     * there is a check to emit next to a table with nothing under that name, or a contract for a
     * behavior the answer said states nothing.
     */
    default Contract contract() {
        return switch (this) {
            case AtTheCallee(Contract c) -> c;
            case AtEachCrossing(Contract c) -> c;
            case NoContract _ -> null;
        };
    }

    /**
     * Every {@link AbortKind} a run of the crossing this enforces can end without a value for:
     * {@link AbortKind#ENSURES_NOT_HELD} where something here actually checks a clause, and
     * {@link AbortSet#NONE} where {@link NoContract} says there is no clause to check — a
     * conclusion, reached by reading what the behavior declared.
     *
     * <p>This is the {@code ensures} half of what {@link souther.compiler.abort.AbortSites} answers
     * for a {@code Core} site — not folded into that walker, because where a clause is checked is
     * already a semantic object of its own and asking it a second question here is cheaper and more
     * honest than reading the same fact out of a tree walk.
     */
    default AbortSet aborts() {
        return switch (this) {
            case AtTheCallee _ -> AbortSet.of(AbortKind.ENSURES_NOT_HELD);
            case AtEachCrossing _ -> AbortSet.of(AbortKind.ENSURES_NOT_HELD);
            case NoContract _ -> AbortSet.NONE;
        };
    }

    /**
     * What {@code decided}, the compilation of {@code module}, says about {@code behavior}, one of
     * {@code module}'s own.
     *
     * <p>A table of a module's own decisions is asked about its own behaviors only: what a caller
     * reads of another module's behavior is that behavior's projection, made by the same rule
     * ({@link #of}) from the same facts. So a miss is a table that was not filled — or a behavior of
     * another module asked of the wrong table — and is this compiler failing either way.
     */
    public static EnsuresEnforcement in(Map<ValueName.Behavior, EnsuresEnforcement> decided,
                                        String module, ValueName.Behavior behavior) {
        EnsuresEnforcement answered = decided.get(behavior);
        if (answered == null) {
            throw new IllegalStateException("no enforcement decision for `" + behavior + "` in the"
                    + " table `" + module + "`'s compilation decided for its own behaviors");
        }
        return answered;
    }

    /**
     * What is being done about a behavior's clause, read from what it declares ({@code contract},
     * null where it declares nothing) and from whether Java supplies its body.
     *
     * <p>The one place the two facts meet. Both are facts about the behavior as the module that
     * declares it has it, so the answer is the same whoever asks: the compilation of that module
     * placing its checks, and a run standing something in for the behavior asking what the
     * implementation it replaced would have checked. {@code injected} is the classification the
     * declaring module answers ({@code Bodies.Implementation}), and not the set the backend goes on
     * adding to, where a behavior this module gives a body to but reaches as a dependency joins the
     * injected ones.
     */
    public static EnsuresEnforcement of(Contract contract, boolean injected) {
        if (contract == null) {
            return NoContract.INSTANCE;
        }
        return injected ? new AtEachCrossing(contract) : new AtTheCallee(contract);
    }
}
