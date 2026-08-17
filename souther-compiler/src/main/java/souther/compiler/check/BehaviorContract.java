package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.CaseSelector;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * What a behavior declares about the relation between what it is given and what it answers, read
 * once and specialized once.
 *
 * <p>Five readers want this: the check that a clause is well formed, the emitter that turns it into
 * the method a violation is found by, the classification that says how much of it a caller can
 * assume, the editor that shows that classification, and the analysis that assumes it at a call.
 * Each of them wants the clause resolved, typed, and split into the cases the answer can be. Doing
 * that once is what this is for — a reader arriving here does not go back to {@link Hir} for what a
 * case means or for what the parameters are called.
 *
 * <p>Typed once is not one tree. The language has two readings of an expression — the one that runs,
 * with the operations it is made of inlined, and the one the analysis reads, with the operations it
 * knows the meaning of left standing ({@link Terms.Of}) — and a rule is read as either. What is done
 * once is the resolving, the typing and the specialization; which tree a reader gets is that
 * reader's own question and is answered from the same rule.
 */
public record BehaviorContract(ValueName.Behavior behavior, List<ContractParam> params, Type output,
                        List<Clause> clauses) {

    public BehaviorContract {
        params = List.copyOf(params);
        clauses = List.copyOf(clauses);
    }

    /**
     * A parameter as a rule names it: where it is bound, what the author calls it, what it holds, and
     * which one it is.
     *
     * <p>A rule names it by its binding and never by the spelling. The spelling is carried for a
     * reader — a diagnostic quoting the parameter a rule could not be read against, and an editor
     * showing what a behavior states — which is the reason it is here rather than looked up on the
     * declaration by whoever needs to show one.
     */
    public record ContractParam(BindingId binding, String name, Type type, int index) {}

    /** One `ensures`, with the rules its arms state. A violation is reported by the clause, so this
     *  is what carries the name a reader is given. */
    public record Clause(Optional<String> name, List<Rule> rules, SourcePos pos, Region region) {

        public Clause {
            rules = List.copyOf(rules);
        }
    }

    /**
     * One statement: what has to be so of the answer for it to apply, and what is then so.
     *
     * <p>A rule is already specialized — there is one per case an arm names, because {@code value}
     * is read as what that case holds and the cases hold different things. So a reader does not
     * specialize again, and the identity of what it is reading is the rule's own.
     */
    public record Rule(Guard guard, BindingId value, Hir.Expr statement, RuleId id, SourcePos pos) {

        /** What {@code value} is read as here: what the case holds, or the whole answer where the
         *  rule applies to every answer. */
        public Type valueType(Type output) {
            return guard instanceof Guard.Case c ? c.selector().bound() : output;
        }
    }

    /**
     * When a rule applies.
     *
     * <p>Rules are not tried in order and one answer may satisfy several guards — a data may be a
     * case of two sums declared in its module — so every rule whose guard holds is a rule the answer
     * is held to. That is what a declaration says; taking the first is what a {@code match} does,
     * and a declaration has no order to read.
     */
    public sealed interface Guard {

        /** The rule applies to every answer: the form written where the answer has no cases. */
        public record Always() implements Guard {}

        /** The rule applies where the answer is this case. */
        public record Case(CaseSelector selector) implements Guard {}
    }

    /**
     * Which rule this is: where in the declaration it is written, and which case it is about.
     *
     * <p>Coordinates in the declaration and not steps of a walk. Which clause, which arm of it, and
     * which case that arm names is what the author wrote; nothing here comes from the order some
     * reader happened to visit things in, so two readings of one declaration — the tree that runs and
     * the tree the analysis reads — answer with the same ids without having to be matched up
     * afterwards.
     *
     * <p>{@code arm} is needed and {@code (clause, selector)} would not do: two arms of one clause may
     * name the same case, and {@code Found -> p | Found -> q} is two rules. It moves when arms are
     * added, removed or reordered, which is the declaration changing shape — not something else in the
     * module moving.
     *
     * <p>It counts the arms of the whole behavior and not of its clause, so the arms of the second
     * clause carry on from where the first left off. That is what the binding {@code value} is is
     * numbered by, and one number for both is one thing to keep true instead of two.
     */
    public record RuleId(ValueName.Behavior behavior, int clause, int arm, TypeSymbol selector) {}

    /** Every rule, in the order the clauses and their arms are written. */
    public List<Rule> rules() {
        List<Rule> out = new ArrayList<>();
        for (Clause clause : clauses) {
            out.addAll(clause.rules());
        }
        return out;
    }

    /** The clause a rule was written under, which is what a violation of it is reported by. */
    public Clause clauseOf(Rule rule) {
        return clauses.get(rule.id().clause());
    }

    /** Whether this behavior states anything at all. */
    public boolean isEmpty() {
        return clauses.isEmpty();
    }

    /** The names a rule reads its parameters and its answer under. */
    public static BindingOwner ownerOf(ValueName.Behavior behavior) {
        return new BindingOwner.OfSignature(behavior);
    }
}
