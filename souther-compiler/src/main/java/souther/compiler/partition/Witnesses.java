package souther.compiler.partition;

import souther.compiler.ast.Ast;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Values built to hold what a rule says a value must hold.
 *
 * <p>What stands for a type used to come from the carrier alone — the empty one for every collection,
 * one character for a string — and a rule saying the collection is not empty is then the one rule that
 * refuses the one value on offer. Read the minimum before the value is chosen and it is instead the
 * size the value is built at.
 *
 * <p>Proposals, and several of them. Nothing here decides whether a newtype accepts what it is handed:
 * that is the decoder's answer and it is asked afterwards, which is what lets a value be built from the
 * part of a rule this can read while the rest of the rule refuses it. A position offering one value is
 * exactly the defect this is about, so a collection is offered one proposal per value its element
 * offers rather than one built from the first of them — an element that proposes a format and a minimum
 * would otherwise have the choice between them made here, a level below where it was left open.
 *
 * <p>Per element and not across them. What a row is searched for is already the product of what its
 * positions offer, and taking a product again inside one position would spend that search on
 * assignments the position is not what they are about.
 *
 * <p>A tree, because a collection holds values that have rules of their own, and what stands for a list
 * of a newtype is what stands for that newtype in a list. That question is the one the position itself
 * asked, so it is asked of the same chooser. A type written in terms of itself would ask it forever, so
 * the names being expanded are carried down and a name met twice is given up on — which is the right
 * answer there, since no value of such a type exists.
 */
final class Witnesses {

    /** How many proposals one collection is worth. Each is another assignment for the search around it
     * to walk, and the values past a few are variations on the ones before them. */
    private static final int MAX_PROPOSALS = 3;

    /**
     * Values of {@code carrier} holding at least {@code least} of whatever counts it, or none where
     * this can build none.
     *
     * <p>The minimum itself and not one element. Recognising {@code >= 3} and then offering a list of
     * one would refuse the row for the reason the empty list was refused, having read the rule and not
     * used it.
     */
    static List<FixtureTemplate> holding(Type carrier, int least, Symbols symbols,
                                         Set<TypeName> expanding) {
        if (carrier == null || least <= 0) {
            return List.of();
        }
        // A string is counted by its characters, and one character is as good as another where the
        // rule is about how many there are. What a format asks for instead is a proposal of its own,
        // put beside this one by the caller.
        if (carrier == Type.STRING) {
            return List.of(FixtureTemplate.string("x".repeat(least)));
        }
        // A list may hold the same element as many times as it needs to.
        if (carrier instanceof Type.ListOf list) {
            List<FixtureTemplate> out = new ArrayList<>();
            for (FixtureTemplate each : proposalsFor(list.element(), symbols, expanding)) {
                List<FixtureTemplate> elements = new ArrayList<>();
                for (int i = 0; i < least; i++) {
                    elements.add(each);
                }
                out.add(FixtureTemplate.collection(elements));
            }
            return List.copyOf(out);
        }
        // A set of three is three elements no two of which are equal, and a map of three is three
        // entries no two of which share a key. The values under a map's keys are free to repeat.
        if (carrier instanceof Type.SetOf set) {
            List<FixtureTemplate> out = new ArrayList<>();
            for (FixtureTemplate seed : proposalsFor(set.element(), symbols, expanding)) {
                out.add(FixtureTemplate.collection(
                        distinctFrom(seed, set.element(), least, symbols)));
            }
            return List.copyOf(out);
        }
        if (carrier instanceof Type.MapOf map) {
            List<FixtureTemplate> keys = proposalsFor(map.key(), symbols, expanding);
            List<FixtureTemplate> values = proposalsFor(map.value(), symbols, expanding);
            if (keys.isEmpty() || values.isEmpty()) {
                return List.of();
            }
            List<FixtureTemplate> out = new ArrayList<>();
            // Paired off rather than crossed: a key's proposals and a value's are each about their own
            // rules, and a map refused for its keys is not told apart from one refused for its values
            // by trying every combination of the two.
            for (int i = 0; i < Math.min(MAX_PROPOSALS, Math.max(keys.size(), values.size())); i++) {
                FixtureTemplate value = values.get(Math.min(i, values.size() - 1));
                List<FixtureTemplate> entries = new ArrayList<>();
                for (FixtureTemplate key : distinctFrom(keys.get(Math.min(i, keys.size() - 1)),
                        map.key(), least, symbols)) {
                    entries.add(FixtureTemplate.entry(key, value));
                }
                out.add(FixtureTemplate.collection(entries));
            }
            return List.copyOf(out);
        }
        return List.of();
    }

    /** What the position at {@code type} would itself be offered, which is what a value built around it
     * has to keep offering. */
    private static List<FixtureTemplate> proposalsFor(Type type, Symbols symbols,
                                                      Set<TypeName> expanding) {
        List<FixtureTemplate> stands = Partitions.representativesOf(type, symbols, null, expanding);
        return stands.size() <= MAX_PROPOSALS ? stands : stands.subList(0, MAX_PROPOSALS);
    }

    /**
     * {@code seed} and up to {@code least} values in all, no two of them equal.
     *
     * <p>The ones past the seed come from inside the type's own rules rather than from a count started
     * at nothing: a number stepped through the range its invariant leaves, a string one character
     * longer than the minimum it has to meet. A second value the element itself refuses would have the
     * collection refused for its elements while saying nothing about its size.
     *
     * <p>Fewer than asked where this runs out, which is not the same as failing. A set of three
     * booleans is a thing no value satisfies, and offering the two that exist is a proposal the decoder
     * answers the way it answers any other.
     */
    private static List<FixtureTemplate> distinctFrom(FixtureTemplate seed, Type type, int least,
                                                      Symbols symbols) {
        Set<String> written = new LinkedHashSet<>();
        List<FixtureTemplate> out = new ArrayList<>();
        written.add(seed.text());
        out.add(seed);
        for (int i = 0; out.size() < least; i++) {
            FixtureTemplate each = varied(type, i, symbols);
            if (each == null) {
                break;
            }
            if (written.add(each.text())) {
                out.add(each);
            }
        }
        return List.copyOf(out);
    }

    /**
     * The {@code index}th value of {@code type} this can name, or null where the carrier has no order
     * it can walk.
     *
     * <p>A string grows by a character from the length its rules ask for, and a whole number steps
     * through the range they leave. A date or a record has no such step that keeps every rule the
     * position carries, and inventing one would put a value in a row the type's own chooser had reason
     * not to offer.
     */
    private static FixtureTemplate varied(Type type, int index, Symbols symbols) {
        Type carrier = TypeOps.base(type, symbols);
        if (carrier == Type.STRING) {
            return wrapped(type, FixtureTemplate.string(
                    "x".repeat(Math.max(1, Partitions.leastHeld(type, symbols)) + index)), symbols);
        }
        BigDecimal number = Partitions.numberInside(type, symbols, index);
        if (number == null) {
            return null;
        }
        return wrapped(type, carrier == Type.DECIMAL ? FixtureTemplate.decimal(number)
                : FixtureTemplate.integer(number.longValueExact()), symbols);
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
