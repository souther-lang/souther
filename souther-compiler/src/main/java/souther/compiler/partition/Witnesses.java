package souther.compiler.partition;

import souther.compiler.ast.Ast;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * A value built to hold what a rule says it must hold.
 *
 * <p>What stands for a type used to come from the carrier alone — the empty one for every collection,
 * one character for a string — and a rule saying the collection is not empty is then the one rule that
 * refuses the one value on offer. Read the minimum before the value is chosen and it is instead the
 * size the value is built at.
 *
 * <p>A proposal, still. Nothing here decides whether a newtype accepts what it is handed: that is the
 * decoder's answer and it is asked afterwards, which is what lets this be built from the part of a rule
 * it can read while the rest of the rule is left to refuse it. A minimum recognised is a minimum used,
 * and no more is claimed than that — a rule of a shape this cannot read leaves the position with what
 * it had, and a combination whose every candidate is refused is still reported as refused.
 *
 * <p>A tree, because a collection holds values that have rules of their own. What stands for a list of
 * a newtype is a list of what stands for that newtype, which is asked of the same chooser the position
 * itself was asked of. A type written in terms of itself would have this descend forever, so the
 * descent is bounded and gives up rather than inventing a value below the bound.
 */
final class Witnesses {

    /** How far a value may be built inside another before this stops. Reached only by a type written
     * in terms of itself, which no witness exists for anyway. */
    static final int MAX_DEPTH = 4;

    /**
     * A value of {@code carrier} holding at least {@code least} of whatever counts it, or null where
     * this can build none.
     *
     * <p>The minimum itself and not one element. Recognising {@code >= 3} and then offering a list of
     * one would refuse the row for the reason the empty list was refused, having read the rule and not
     * used it.
     */
    static FixtureTemplate holding(Type carrier, int least, Symbols symbols, int depth) {
        if (carrier == null || least <= 0 || depth > MAX_DEPTH) {
            return null;
        }
        // A string is counted by its characters, and one character is as good as another where the
        // rule is about how many there are.
        if (carrier == Type.STRING) {
            return FixtureTemplate.string("x".repeat(least));
        }
        // A list may hold the same element as many times as it needs to.
        if (carrier instanceof Type.ListOf list) {
            FixtureTemplate one = at(list.element(), 0, symbols, depth + 1);
            if (one == null) {
                return null;
            }
            List<FixtureTemplate> elements = new ArrayList<>();
            for (int i = 0; i < least; i++) {
                elements.add(one);
            }
            return FixtureTemplate.collection(elements);
        }
        // A set of three is three elements no two of which are equal, and a map of three is three
        // entries no two of which share a key. The values under a map's keys are free to repeat.
        if (carrier instanceof Type.SetOf set) {
            List<FixtureTemplate> elements = distinct(set.element(), least, symbols, depth + 1);
            return elements.isEmpty() ? null : FixtureTemplate.collection(elements);
        }
        if (carrier instanceof Type.MapOf map) {
            List<FixtureTemplate> keys = distinct(map.key(), least, symbols, depth + 1);
            FixtureTemplate value = at(map.value(), 0, symbols, depth + 1);
            if (keys.isEmpty() || value == null) {
                return null;
            }
            List<FixtureTemplate> entries = new ArrayList<>();
            for (FixtureTemplate key : keys) {
                entries.add(FixtureTemplate.entry(key, value));
            }
            return FixtureTemplate.collection(entries);
        }
        return null;
    }

    /**
     * Up to {@code many} values of {@code type}, no two of them equal.
     *
     * <p>Fewer where this runs out, which is not the same as failing: a set of three booleans is a
     * thing no value satisfies, and offering the two that exist is a proposal the decoder answers the
     * way it answers any other.
     */
    private static List<FixtureTemplate> distinct(Type type, int many, Symbols symbols, int depth) {
        Set<String> written = new LinkedHashSet<>();
        List<FixtureTemplate> out = new ArrayList<>();
        for (int i = 0; out.size() < many; i++) {
            FixtureTemplate each = at(type, i, symbols, depth);
            if (each == null) {
                break;
            }
            if (written.add(each.text())) {
                out.add(each);
            }
        }
        return out;
    }

    /**
     * The {@code index}th value this can think of for {@code type}, or null where it has no such value.
     *
     * <p>What the position itself offers comes first, so that an element is the value the rest of the
     * generator would have chosen for it and carries whatever its own rules asked for. Past those the
     * value is varied — a longer string, the next whole number — which is the only reason this counts
     * at all: a set needs elements that differ, and a position ordinarily has no reason to offer two.
     */
    private static FixtureTemplate at(Type type, int index, Symbols symbols, int depth) {
        if (depth > MAX_DEPTH) {
            return null;
        }
        List<FixtureTemplate> stands = Partitions.representativesOf(type, symbols, null, depth + 1);
        if (index < stands.size()) {
            return stands.get(index);
        }
        return stands.isEmpty() ? null : varied(type, index, symbols);
    }

    /**
     * A value past the ones already on offer, told apart from them by how it is built.
     *
     * <p>Only where the carrier has an order this can walk. A string grows by a character and a whole
     * number by one; a date or a record has no such step that keeps every rule the position carries,
     * and inventing one would put a value in a row that the type's own chooser had reason not to.
     */
    private static FixtureTemplate varied(Type type, int index, Symbols symbols) {
        Type carrier = TypeOps.base(type, symbols);
        FixtureTemplate bare;
        if (carrier == Type.STRING) {
            // Past the minimum rather than up from one: a longer string keeps a minimum length, which
            // is the rule the position most often carries here.
            bare = FixtureTemplate.string("x".repeat(Math.max(1, Partitions.leastHeld(type, symbols))
                    + index));
        } else if (carrier == Type.INT) {
            bare = FixtureTemplate.integer(index);
        } else {
            return null;
        }
        return wrapped(type, bare, symbols);
    }

    /** The value under every name the position wears, which is how it is written where the position
     * declares a newtype rather than what the newtype carries. */
    private static FixtureTemplate wrapped(Type type, FixtureTemplate bare, Symbols symbols) {
        if (!(type instanceof Type.Ref ref) || !(symbols.get(ref.name()) instanceof Ast.Data data)
                || !data.newtype()) {
            return bare;
        }
        TypeName name = ref.name();
        return FixtureTemplate.newtype(name,
                wrapped(TypeOps.newtypeInner(name, symbols), bare, symbols));
    }

    private Witnesses() {}
}
