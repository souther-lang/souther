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
public record SuppliedRules(Map<BindingOwner, Map<String, RuleIdentity>> byExpansion) {

    /** Nothing recorded, which is what a body handing no rule to anything comes to. */
    public static final SuppliedRules NONE = new SuppliedRules(Map.of());

    public SuppliedRules {
        Map<BindingOwner, Map<String, RuleIdentity>> copy = new LinkedHashMap<>();
        byExpansion.forEach((owner, rules) -> copy.put(owner, Map.copyOf(rules)));
        byExpansion = Map.copyOf(copy);
    }

    /** What {@code expansion} was handed at {@code parameter}, or null where it was handed none. */
    public RuleIdentity at(BindingOwner expansion, String parameter) {
        Map<String, RuleIdentity> rules = byExpansion.get(expansion);
        return rules == null ? null : rules.get(parameter);
    }

    /** Which rules {@code expansion} was handed, empty where it was handed none. */
    public Map<String, RuleIdentity> of(BindingOwner expansion) {
        return byExpansion.getOrDefault(expansion, Map.of());
    }

    /** What is being built while a body is read. */
    public static final class Builder {

        private final Map<BindingOwner, Map<String, RuleIdentity>> byExpansion =
                new LinkedHashMap<>();

        /** Says that {@code expansion} was handed {@code rule} at {@code parameter}. */
        public void handed(BindingOwner expansion, String parameter, RuleIdentity rule) {
            byExpansion.computeIfAbsent(expansion, _ -> new LinkedHashMap<>())
                    .putIfAbsent(parameter, rule);
        }

        public SuppliedRules built() {
            return byExpansion.isEmpty() ? NONE : new SuppliedRules(byExpansion);
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

        /** A declaration named at the call site. Naming it twice hands in one rule. */
        record Named(ValueName declaration) implements RuleIdentity {}

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
