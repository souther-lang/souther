package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.diag.CompileException;

import java.util.Map;

/**
 * A resolved module where a body of it may be expanded — which is where no value of it is defined in
 * terms of itself.
 *
 * <p>A value is substituted at each of its references (ADR-0072), so one that reaches itself is
 * substituted into itself and there is no body to reach the end of. Everything that expands a body
 * needs that to be false, and needs to know before it expands anything: left until the expansion
 * runs out of stack, what comes back names a nesting the author did not write.
 *
 * <p>The condition used to be checked wherever an expansion table was built, which is eleven places
 * in a compile, so the refusal came from whichever of them ran first. Answering whether moved the
 * problem: three questions read the module and expanded it, each said the condition over again, and
 * one of them said it and two did not. This is the answer they wanted — a module that may be
 * expanded — and there is one way to arrive at it.
 *
 * <p>{@link #check} is that way, and it is the check: what it answers exists because
 * {@link ValueCycles} let it. Nothing here takes a tree, so a reader cannot arrive at this state
 * with a module the check was not run over, and a reader that holds one has nothing to remember
 * beside it.
 *
 * <p>It does not hand the tree over. What it claims is not something the payload says, so a reader
 * that took the tree would be holding the module and not the claim — which is how the condition came
 * to be checked in eleven places. A consumer that needs an expandable module says so in its
 * signature, and what it can ask of one is what is written here.
 */
public final class Expandable {

    private final Hir.Module module;

    private Expandable(Hir.Module module) {
        this.module = module;
    }

    /**
     * {@code resolved} where its values are well founded.
     *
     * @throws CompileException where a value of the module is defined in terms of itself, which is
     *     the refusal itself and not a report about the answer being absent
     */
    public static Expandable check(Resolved resolved, Map<String, Hir.FnDef> imported) {
        ValueCycles.rejectIn(resolved.module(), imported);
        return new Expandable(resolved.module());
    }

    /** What the module is called. */
    public String name() {
        return module.name();
    }

    /**
     * The declarations of this module with the names in their invariants written qualified.
     *
     * <p>An alternative representation and not a rung: it is this module's declarations read the way
     * the discharge analysis reads them, and what makes it this carrier's to answer is that reading
     * one expands the helpers a clause names.
     */
    public Hir.Module withQualifiedInvariants() {
        return HelperNames.withQualifiedInvariants(module);
    }

    /** The tree, for the passes of this package that carry the state forward. */
    Hir.Module module() {
        return module;
    }

    @Override
    public boolean equals(Object o) {
        return o instanceof Expandable other && module.equals(other.module);
    }

    @Override
    public int hashCode() {
        return module.hashCode();
    }

    @Override
    public String toString() {
        return module.toString();
    }
}
