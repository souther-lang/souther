package souther.compiler.inputs;

import souther.compiler.check.RuleKey;

/**
 * A name as a rule wrote it: which value's rules are being read, and what those rules call the place
 * the name points at.
 *
 * <p><b>Not a position, and not an absolute path.</b> A clause of a {@code Holder} says
 * {@code q.name} and a clause of the case says {@code name}, and the two may end at the same
 * position without being the same name: what they have in common is settled by resolving them, and
 * settling it here would be this deciding which value's rules reach where. So the value being read
 * is part of the address, and two addresses spelled alike under different values are different
 * addresses.
 *
 * <p>The value is named by where it stands ({@link InputDomain.RuleRoot#at}), which is what already
 * decides what the rules of a value can name ({@link TermPath#ruleKeyUnder}). A second identity for
 * it would be a second answer to the question of which rules reach which positions.
 *
 * <p><b>Every one of these is a name some rule wrote.</b> A path no rule of the value could name
 * makes none — {@link #of} answers null — and that is the reading holding to what it already says
 * about which value's rules reach where. It is not a name that failed to reach anywhere: nothing was
 * written, so there is nothing outstanding.
 *
 * @param root what the rules being read are of, named by where a value of it stands
 * @param key  what those rules call the place, relative to the value —
 *             {@link RuleKey#THE_VALUE} for the value itself
 */
public record RuleAddress(TermPath root, RuleKey key) {

    public RuleAddress {
        if (root == null || key == null) {
            throw new IllegalArgumentException(
                    "an address is somewhere in some value, and the value is part of it");
        }
    }

    /**
     * The address a rule of the value at {@code root} would write for the position at {@code path},
     * or null where no rule of that value can name it.
     *
     * <p>Null for a position under another value as readily as for one no clause can name, which is
     * the one translation between where a position is and what a rule calls it. Read as a name that
     * reached nowhere, a clause of a case would be answering for a position in the sum above it.
     */
    public static RuleAddress of(TermPath root, TermPath path) {
        RuleKey key = path.ruleKeyUnder(root);
        return key == null ? null : new RuleAddress(root, key);
    }

    @Override
    public String toString() {
        return key.isTheValueItself() ? root.toString() : root + "." + key;
    }
}
