package souther.compiler.check;

import souther.compiler.ast.Hir;

import java.util.ArrayList;
import java.util.List;

/**
 * The formal parameters the {@code let} implementing a behavior is required to take (spec
 * §fn-declaration, §depends-on).
 *
 * <p>The behavior's inputs, then the behaviors it depends on in the order they were declared. The
 * order is not a matter of layout: it is what {@link SpecChecker} holds an implementation to, and
 * writing an injected parameter out of that order is E1615. Said here once so that a reader wanting
 * to know the shape — the checker that refuses one, an editor offering to write one — asks rather
 * than works it out again from the signature. Two readings of one rule agree until either moves.
 *
 * <p>Nothing here is about how a parameter is written. Where it goes in a line, and whether the line
 * breaks, is the formatter's.
 */
public final class SpecImplementation {

    private SpecImplementation() {}

    /**
     * One position of the parameter list, told apart by what settles its name.
     *
     * <p>A reader has to do something different with each, which is why they are three and not one
     * name and a flag. What an editor may offer as a hole is exactly what nothing here settles.
     */
    public sealed interface Parameter {

        /**
         * An input. Its position and its type come from the behavior; its name does not — the
         * implementation may call it what it likes — so the behavior's own spelling is a suggestion.
         */
        record Input(String nameSuggestion) implements Parameter {}

        /**
         * An injected behavior. Its position and its name are both settled: it names the behavior it
         * injects, and an implementation that spells it otherwise is refused.
         */
        record Injected(String name) implements Parameter {}

        /**
         * A {@code depends on} entry that reaches no declaration.
         *
         * <p>It takes a position — an implementation still has to have a parameter there — and
         * settles no name for it, since the name it would be held to is the one that was not found.
         * That the clause names nothing is reported where the clause is written, so nothing here
         * says it again.
         */
        record Unanswered() implements Parameter {}
    }

    /** What an implementation of {@code spec} is required to take, in order. */
    public static List<Parameter> parameters(Hir.SpecBehavior spec) {
        List<Parameter> required = new ArrayList<>(spec.params().size() + spec.dependsOn().size());
        for (Hir.Param input : spec.params()) {
            required.add(new Parameter.Input(input.name()));
        }
        for (Hir.Var dependency : spec.dependsOn()) {
            Hir.Var.Denoting named = dependency.answered();
            required.add(named == null
                    ? new Parameter.Unanswered()
                    : new Parameter.Injected(named.bare()));
        }
        return List.copyOf(required);
    }
}
