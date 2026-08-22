package souther.compiler.core;

import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.List;

/**
 * A composed behavior as the checker settled it: what {@link Core} is to a behavior written with a
 * {@code let}, this is to one written with {@code >->}.
 *
 * <p>A composition is an implementation like any other (spec §sequential-composition), and it never
 * had a checked form. The routing a {@code >->} performs — which cases of the running value a stage
 * is offered, and what the running value is after it — was worked out twice from the declaration:
 * once when the composition's own signature was built, and again by the JVM emitter as it wrote the
 * branches. Two derivations of one rule agree until one of them is edited, and the second of them
 * was in a backend, which is where a decision about what a Souther program means may not be made.
 *
 * <p>What is here is the decision and not a plan for carrying it out. Every backend that emits this
 * composition must offer a stage the same cases and take the same value onward, or the program
 * means something different depending on what it was compiled to. How that is realised — a branch,
 * a jump, a table, a block — is the backend's, and none of it is written down here.
 */
public record Composition(List<Stage> stages, Type answers) {

    public Composition {
        if (stages.isEmpty()) {
            throw new IllegalArgumentException("a composition composes something");
        }
        stages = List.copyOf(stages);
    }

    /**
     * One stage: the behavior it applies, what that behavior answers, and when it is applied.
     *
     * <p>{@code answers} is the stage's own output and not the running value after it. The two
     * differ exactly when the stage was offered part of what was running: the cases it did not
     * accept have left the main line and are not offered onward (spec §type-routing), and a stage
     * later on is held to what it can be given, not to everything the composition ever carried.
     */
    public record Stage(ValueName.Behavior behavior, Type answers, Routing routing) {}

    /** When a stage is applied to the running value. */
    public sealed interface Routing {

        /** Always: the first stage, which takes the composition's own arguments, and any stage
         *  whose running value carries no cases to tell apart. */
        record Always() implements Routing {}

        /** Only where the running value is one of {@code accepted}. Anything else has left the main
         *  line, and the composition answers with it rather than offering it to what follows. */
        record OnCases(List<TypeSymbol> accepted) implements Routing {

            public OnCases {
                accepted = List.copyOf(accepted);
            }
        }
    }
}
