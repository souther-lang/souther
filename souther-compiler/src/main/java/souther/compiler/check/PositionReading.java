package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * What the model writes at a position, before any value stands there.
 *
 * <p>The one step every reading of a declaration takes. Which declarations state something of every
 * value here, what is readable on such a value, and what stands below that no reading here takes in
 * are three facts about a type, and every reader of a position wants some of them. Each working them
 * out from the declaration is how a sum comes to be a position that states nothing to one reader, a
 * position with a readable field to a second, and a class with an accessor to a third.
 *
 * <p><b>What kind of position this is, is {@link Shape}'s answer, and the shared part of a sum is
 * part of that answer.</b> Nothing here resolves a name to a declaration to find out what kind of
 * thing it is; {@link TypeView} has done that, and this says what the model writes at each kind.
 *
 * <p>Nothing here reads a clause, a value, or a path. What a clause states of a value in hand is
 * {@link TypeGuarantees}, which asks this where it starts; how far to walk is
 * {@link GuaranteeWalk}'s. Held together, the depth a reader could afford would be part of what a
 * declaration means.
 *
 * @param entering  the declaration standing here, which a walk files what it has entered under and
 *                  a reader supposing values names, or null where no declaration stands here. Not
 *                  {@link #owners}: a sum whose cases share nothing declares nothing of every value
 *                  here and is a declaration a walk has entered all the same
 * @param owners    the declarations whose clauses hold of every value standing here. One for a
 *                  record or a newtype; for a sum, the declarations its cases share — a rule written
 *                  on one case refuses values of that case and not every value here
 * @param fields    what is readable on a value here, in the order it is declared
 * @param atOwnPath whether those fields are at paths of their own. A newtype's {@code value} is not:
 *                  wearing a name is not being somewhere else
 * @param handedOn  what stands under this position that no reading here takes in — the cases of a
 *                  sum, what a container holds
 */
record PositionReading(TypeSymbol entering, List<Owner> owners, Map<String, Type> fields,
                       boolean atOwnPath, List<Type> handedOn) {

    /** A declaration whose clauses hold of every value standing at a position, and the name it was
     *  reached by — which is what a clause of it resolves its fields against. */
    record Owner(TypeSymbol.AtModule named, Hir.Data data) {}

    PositionReading {
        owners = List.copyOf(owners);
        handedOn = List.copyOf(handedOn);
    }

    private static PositionReading nothing(TypeSymbol entering) {
        return new PositionReading(entering, List.of(), Map.of(), true, List.of());
    }

    /** What the model writes at a position of {@code type}. */
    static PositionReading of(Type type, Symbols symbols) {
        TypeView view = TypeView.of(type, symbols);
        if (view.isWrapped()) {
            // One name at a time. What the layer states is stated of this very atom, and what the
            // value under it states is read where a walk reaches it.
            TypeOps.Layer worn = view.wrappers().getFirst();
            return new PositionReading(worn.named(), owning(worn.named(), symbols),
                    TypeOps.fieldTypes(worn.data(), symbols), false, List.of());
        }
        return switch (view.shape()) {
            // What is readable off a value here, which is the fields for a record.
            case Shape.Product product -> {
                ReadableFields readable = ReadableFields.of(product);
                yield new PositionReading(product.name(), owning(readable.declaredBy(), symbols),
                        readable.fields(), true, List.of());
            }
            // A sum is a common product times a choice of case. What the cases share is stated of
            // every value standing here and is readable on one; what one case declares is under that
            // case, and a reading of it is opened where a match opens the case.
            case Shape.Sum sum -> {
                ReadableFields readable = ReadableFields.of(sum);
                yield new PositionReading(sum.name(), owning(readable.declaredBy(), symbols),
                        readable.fields(), true, cases(sum.name(), symbols));
            }
            // A unit data holds nothing and may write no rule about it (spec §unit-data), and a
            // primitive is written under no declaration of its own.
            case Shape.Unit unit -> nothing(unit.name());
            case Shape.Scalar _ -> nothing(null);
            // What a container holds, what an option holds when it holds anything, an unnamed
            // union's members, a tuple's elements. Each is a value a reading of its own is opened
            // at, and none of them is a value standing here.
            case Shape.Cases _, Shape.Sequence _, Shape.Mapping _, Shape.Optional _, Shape.Tuple _,
                 Shape.Function _ -> new PositionReading(null, List.of(), Map.of(), true,
                         held(type));
            // Nothing was interpreted, so nothing is written here and nothing is under it.
            case Shape.Unresolved _, Shape.Uninhabited _, Shape.Bottom _, Shape.Erroneous _,
                 Shape.Undecided _ -> nothing(null);
        };
    }

    /**
     * The positions a value here has of its own, each at the name it is reached by.
     *
     * <p>Empty for a position whose contents are at no path of its own — a newtype is the value it
     * wraps, and a caller stepping into one would file every position under it one step too deep.
     */
    Map<String, Type> positionsUnder() {
        return atOwnPath ? fields : Map.of();
    }

    private static List<Owner> owning(TypeSymbol name, Symbols symbols) {
        return owning(List.of(name), symbols);
    }

    /** The declarations these names denote, leaving out any that denotes none. */
    private static List<Owner> owning(List<TypeSymbol> names, Symbols symbols) {
        List<Owner> out = new ArrayList<>();
        for (TypeSymbol name : names) {
            Owner owner = TypeOps.writingFields(name, symbols);
            if (owner != null) {
                out.add(owner);
            }
        }
        return out;
    }

    /** A sum's cases, as the one closure over them answers. */
    private static List<Type> cases(TypeSymbol sum, Symbols symbols) {
        List<Type> out = new ArrayList<>();
        for (TypeSymbol leaf : AtomSpace.subjectAtoms(Type.ref(sum), symbols)) {
            out.add(Type.ref(leaf));
        }
        return out;
    }

    /** The types a compound holds. */
    private static List<Type> held(Type type) {
        List<Type> out = new ArrayList<>();
        Type.forEachChild(type, out::add);
        return out;
    }
}
