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
 * <p>Which definition implements a behavior is answered here as well ({@link #implementedBy}), and
 * for the same reason: a caller that found the definition itself would then divide its parameters
 * itself, and the division is this rule.
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

    /**
     * The definition implementing a behavior, and which of its parameters are the declared inputs.
     *
     * <p>A value rather than the list alone, so that having found a definition and having found one
     * that takes nothing stay two answers. A behavior of no inputs is implemented by a {@code let}
     * of no parameters, and a caller handed an empty list for both would have to decide which it
     * was looking at.
     *
     * <p>The inputs and not also the trailing parameters the {@code depends on} clause is answered
     * by. Nothing reads those as a list: {@link SpecChecker#dependencyBindings} walks them against
     * the clause, and it runs while E1614 is still being decided — where this refuses a list too
     * short to divide, that one carries on and lets the diagnostic be the report. Divided here as
     * well, the two would be one rule with two strictnesses.
     */
    public record Implemented(Hir.FnDef definition, List<Hir.FnParam> inputs) {

        public Implemented {
            inputs = List.copyOf(inputs);
        }
    }

    /**
     * The {@code let} of {@code module} implementing {@code spec}, or null where the module has
     * none — an injected behavior and an unwritten one both reach this and neither has a definition.
     *
     * <p>Among what the module declared, and not among what it took on to emit. What a module emits
     * without declaring is a recursion another module wrote and a method minted for a row's operand
     * ({@code Hir.Module#takenOn}); a behavior's implementation is a {@code let} of its name and is
     * always a declaration. {@link Requirements#implementationOf} decides whether a behavior has one
     * by looking in the same place, so a name found here is a name that reading called implemented.
     *
     * <p>How many parameters the definition is required to have is {@link SpecChecker}'s, reported
     * as E1614 where it disagrees. Nothing is restated here: what this refuses is the state where
     * the division cannot be made at all, which is not a program being wrong but that check not
     * having run. So this is for a reader standing after the check — the emitter, the snapshot — and
     * not for the checker deciding it.
     */
    public static Implemented implementedBy(Hir.Module module, Hir.SpecBehavior spec) {
        Hir.FnDef definition = null;
        for (Hir.FnDef fn : module.fns()) {
            if (fn.name().equals(spec.name())) {
                definition = fn;   // the last, as every reader keying these by name keeps
            }
        }
        if (definition == null) {
            return null;
        }
        int inputs = spec.params().size();
        if (definition.params().size() < inputs) {
            throw new IllegalStateException("`" + module.name() + "." + spec.name() + "` takes "
                    + inputs + " and its implementation has " + definition.params().size()
                    + " parameters to divide");
        }
        return new Implemented(definition, definition.params().subList(0, inputs));
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
                    : new Parameter.Injected(named.denotes().name()));
        }
        return List.copyOf(required);
    }
}
