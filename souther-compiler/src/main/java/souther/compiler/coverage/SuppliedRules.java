package souther.compiler.coverage;

import souther.compiler.types.BindingOwner;
import souther.compiler.types.RuleOrigin;
import souther.compiler.types.ValueName;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Which rule each expansion was handed, by the parameter it was handed to.
 *
 * <p>Recorded where the call site is read, which is the one place that has it. After the rule is
 * spliced in, what is left is the rule's body standing where a parameter was, and telling that from
 * an argument the rule reads is the thing no reading of the tree can do.
 *
 * <p>A rule is what was written and not where it was handed over. Two call sites naming one
 * declaration hand in one rule, and a row through the arms of one is a row through that rule: asked
 * per hand-over, the second is owed a row that establishes what the first already did. Two call
 * sites writing the same expression are two rules — the author wrote two, and nothing here says they
 * agree.
 */
public record SuppliedRules(Map<BindingOwner, Handed> byExpansion) {

    /** Nothing recorded, which is what a body handing no rule to anything comes to. */
    public static final SuppliedRules NONE = new SuppliedRules(Map.of());

    public SuppliedRules {
        byExpansion = Map.copyOf(byExpansion);
    }

    /**
     * What one copy of a declaration was handed.
     *
     * <p>Which declaration it is a copy of, beside what it was handed. A parameter's name says which
     * of a declaration's own parameters it is and nothing more — two declarations name a parameter
     * alike as often as not — so a reader looking for the copy that owns a parameter by its name
     * finds whichever copy spells one that way, which is the innermost one as often as the right
     * one.
     */
    public record Handed(souther.compiler.types.ReachName.Declaration declaration,
                         Map<String, RuleIdentity> rules) {

        public Handed {
            rules = Map.copyOf(rules);
        }
    }

    /** What {@code expansion} was handed at {@code parameter}, or null where it was handed none. */
    public RuleIdentity at(BindingOwner expansion, String parameter) {
        Handed handed = byExpansion.get(expansion);
        return handed == null ? null : handed.rules().get(parameter);
    }

    /** Which declaration {@code expansion} is a copy of, or null where nothing here says.
     *  As the reference that reached it — what a call carries, and what
     *  {@link DecisionSource.Supplied#declaration} is, so the two are compared as identities and
     *  not as two spellings that happen to agree. */
    public souther.compiler.types.ReachName.Declaration declarationOf(BindingOwner expansion) {
        Handed handed = byExpansion.get(expansion);
        return handed == null ? null : handed.declaration();
    }

    /** What is being built while a body is read. */
    public static final class Builder {

        private final Map<BindingOwner, souther.compiler.types.ReachName.Declaration> of =
                new LinkedHashMap<>();
        private final Map<BindingOwner, Map<String, RuleIdentity>> byExpansion =
                new LinkedHashMap<>();

        /** Says that {@code expansion} is a copy of {@code declaration} and was handed {@code rule}
         *  at {@code parameter}. */
        public void handed(BindingOwner expansion, souther.compiler.types.ReachName.Declaration declaration,
                           String parameter, RuleIdentity rule) {
            of.putIfAbsent(expansion, declaration);
            byExpansion.computeIfAbsent(expansion, _ -> new LinkedHashMap<>())
                    .putIfAbsent(parameter, rule);
        }

        public SuppliedRules built() {
            if (byExpansion.isEmpty()) {
                return NONE;
            }
            Map<BindingOwner, Handed> out = new LinkedHashMap<>();
            byExpansion.forEach((owner, rules) -> out.put(owner, new Handed(of.get(owner), rules)));
            return new SuppliedRules(out);
        }
    }

    /**
     * Which rule was handed in.
     *
     * <p>What the author wrote, and not how it reached the parameter. A rule handed on through a
     * helper is the rule the outermost call site wrote: the helper's own parameter is substituted
     * before its body is expanded, so what arrives here is already what was written.
     */
    public sealed interface RuleIdentity {

        /**
         * A declaration named at the call site. Naming it twice hands in one rule.
         *
         * <p>A declaration and never a binding. A binding is where a rule was put, and there are as
         * many of those as there are copies of the body that put it there — so one rule read out of
         * a name would be as many rules as the body has copies, and two names for one declaration
         * would be two.
         */
        record Named(ValueName declaration) implements RuleIdentity {

            public Named {
                if (declaration instanceof ValueName.Local) {
                    throw new IllegalArgumentException(
                            "a rule is a declaration, and a binding is where one was put: "
                                    + declaration);
                }
            }
        }

        /**
         * A rule the source wrote out, told from every other by which block of that source it is.
         *
         * <p>Its origin and not its position. A copy of a body a reader cannot open is stamped with
         * the call site that spliced it, so two rules written in one library helper come to one
         * position and one rule copied to two call sites comes to two — the first counts two rules
         * as one, and the second asks for a row establishing what another already does.
         */
        record Written(RuleOrigin rule) implements RuleIdentity {

            public Written {
                if (!rule.isWritten()) {
                    throw new IllegalArgumentException(
                            "a rule told apart by which block it is was written by some source");
                }
            }
        }
    }
}
