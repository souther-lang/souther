package souther.compiler.partition;

import souther.compiler.ast.Ast;
import souther.compiler.check.Shape;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.check.TypeView;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;

import java.util.ArrayList;
import java.util.List;

/**
 * The classes a type states its values fall into, read through every name they are written under.
 *
 * <p>The one reading of what a declaration states. What a position divides into, what a witness of
 * a type varies over, and what values stand for one of its cases were three readings of one
 * declaration, and they disagreed about how far to look through a name.
 *
 * <p>Classes read off a type, and not every class there is: what a body's comparisons divide a
 * position into is read where those are ({@link Intervals}, and the values a {@code guard} singles
 * out), and both kinds end up on one axis. So an empty answer here is this reading finding nothing
 * stated, which the phase that owns it says ({@link LocalInspection}).
 */
final class PartitionClasses {

    static List<PartitionClass> of(Type type, Symbols symbols) {
        return of(TypeView.of(type, symbols), symbols);
    }

    /**
     * The class evidence this producer derives from a position's type, read through every name it
     * is written under.
     *
     * <p>Through the names, because a newtype is the value it wraps (spec §primitives): a
     * {@code data StageN = Stage} is the sum {@code Stage} and divides into its cases. Which is not
     * what this asked before — it asked whether the type it was handed was a sum, stopped at the
     * name, and reported a position the model divides three ways as one it divides no way (issue
     * #631). The line drawn on that same position read straight through the name, so the two
     * readings of one declaration disagreed.
     *
     * <p>And under them, because that is how a row writes the value. The names come off to say what
     * the position is and go back on to say what stands at it — one fact, read from
     * {@link TypeView} once, rather than each reader deciding again how far to look.
     *
     * <p><b>Empty is this producer having no class evidence, and never that the position has no
     * classes.</b> The two read the same and are not the same claim: the second is a statement
     * about the model, and it is not one this is in a position to make — the rules a body writes
     * have not been read, and what is under the position has not been asked. A
     * {@link Shape.Unresolved} answers empty here and is reported as a type this could not
     * interpret, which the structural reading after this one supplies. Making the conclusion here
     * is the defect the whole protocol is against, in one function.
     *
     * <p>Exhaustive over {@link Shape}, with no {@code default}, so that a shape added later stops
     * this compiling rather than arriving as a position this quietly has no evidence about.
     *
     * <p>Nothing about the rules on the position. What its type declares and what its rules leave
     * it able to hold are two facts, and this is the first of them — crossed with the second by
     * {@link LocalInspection}, which is where a case the model refuses stops being a class.
     */
    static List<PartitionClass> of(TypeView view, Symbols symbols) {
        List<TypeName> worn = view.wrappers().stream().map(TypeOps.Layer::named).toList();
        return switch (view.shape()) {
            // A `Bool` is two values. No other primitive has classes to read off its type: what a
            // number's rules leave is a range with edges — everything outside a newtype's invariant
            // is refused at construction (E1903), so there is no class on the other side to cover —
            // and what does divide a number is a threshold, which is read from a body and not here.
            case Shape.Scalar scalar -> scalar.prim() == Type.Prim.BOOL
                    ? eitherWay(worn) : List.of();
            case Shape.Sum sum -> caseClasses(Type.ref(sum.name()), worn, symbols);
            case Shape.Cases cases -> caseClasses(Type.union(cases.members()), worn, symbols);
            case Shape.Optional optional -> heldOrNot(optional.element(), worn, symbols);
            // Shapes whose types state no division of their own. A record is made of positions and a
            // collection holds its values inside something — what that comes to is the structural
            // reading's answer, not this one's — and a unit data has one value, which no class of
            // this producer's tells from another.
            case Shape.Product _, Shape.Unit _, Shape.Sequence _, Shape.Mapping _,
                 Shape.Tuple _, Shape.Function _,
            // And the five that are not value shapes: nothing here was interpreted, so there is
            // nothing to read classes off. What that means for the position is said where the
            // provenance is, which is what the shape carries into the phase after this one.
                 Shape.Uninhabited _, Shape.Bottom _, Shape.Erroneous _, Shape.Undecided _,
                 Shape.Unresolved _ -> List.of();
        };
    }

    /** The two values of a {@code Bool}, under the names the position writes them under. */
    private static List<PartitionClass> eitherWay(List<TypeName> worn) {
        return List.of(
                PartitionClass.of("true", "true",
                        Classifier.under(worn, Classifier.byShape(v -> isBool(v, true))),
                        RepresentativeSource.under(worn,
                                RepresentativeSource.of(FixtureTemplate.bool(true)))),
                PartitionClass.of("false", "false",
                        Classifier.under(worn, Classifier.byShape(v -> isBool(v, false))),
                        RepresentativeSource.under(worn,
                                RepresentativeSource.of(FixtureTemplate.bool(false)))));
    }

    /** Whether an optional holds anything, which is the one division its type makes. */
    private static List<PartitionClass> heldOrNot(Type element, List<TypeName> worn,
                                                  Symbols symbols) {
        List<FixtureTemplate> some = Partitions.representativesOf(element, symbols);
        return List.of(
                PartitionClass.of("None", "None",
                        Classifier.under(worn,
                                Classifier.byShape(v -> v instanceof ObservedValue.Absent)),
                        RepresentativeSource.under(worn,
                                RepresentativeSource.of(FixtureTemplate.none()))),
                some.isEmpty()
                        ? PartitionClass.ungeneratable("Some", "Some",
                                Classifier.under(worn, Classifier.byShape(
                                        v -> !(v instanceof ObservedValue.Absent))),
                                "nothing here composed a value of " + Type.show(element))
                        : PartitionClass.of("Some", "Some",
                                Classifier.under(worn, Classifier.byShape(
                                        v -> !(v instanceof ObservedValue.Absent))),
                                RepresentativeSource.under(worn,
                                        RepresentativeSource.of(some))));
    }

    /** A sum's cases, each a class, under the names the position writes them under. */
    private static List<PartitionClass> caseClasses(Type sum, List<TypeName> worn,
                                                    Symbols symbols) {
        List<PartitionClass> cases = new ArrayList<>();
        for (TypeName leaf : TypeOps.leafCases(sum, symbols)) {
            cases.add(caseClass(leaf, worn, symbols));
        }
        return cases;
    }

    /** What a case's class is called, in one place: a reading that decides which cases the position
     *  holds names the same classes the reading above builds. */
    static String idOfCase(TypeName leaf) {
        return leaf.name();
    }

    private static PartitionClass caseClass(TypeName leaf, List<TypeName> worn, Symbols symbols) {
        Classifier is = Classifier.under(worn, Classifier.byShape(v -> switch (v) {
            case ObservedValue.Unit u -> leaf.equals(u.type());
            case ObservedValue.Constructed c -> leaf.equals(c.type());
            default -> false;
        }));
        if (!(symbols.get(leaf) instanceof Ast.Data data)) {
            return PartitionClass.of(idOfCase(leaf), leaf.name(), is,   // naming it builds it
                    RepresentativeSource.under(worn,
                            RepresentativeSource.of(FixtureTemplate.unitCase(leaf))));
        }
        if (data.newtype()) {
            List<FixtureTemplate> inner = Partitions.insideTheNewtype(leaf, symbols);
            return inner.isEmpty()
                    ? PartitionClass.ungeneratable(idOfCase(leaf), leaf.name(), is,
                            "nothing here composed a value of what `" + leaf.name() + "` wraps")
                    : PartitionClass.of(idOfCase(leaf), leaf.name(), is,
                            RepresentativeSource.under(worn, RepresentativeSource.under(
                                    List.of(leaf), RepresentativeSource.of(inner))));
        }
        // A record case is written field by field, which is the generator's composition. So the class
        // names the constructor and the generator does the composing — the same walk every other
        // record goes through, rules between the fields and all. Under the position's names either
        // way: what is composed is an `Approved`, and what the row writes is `DecisionN(Approved
        // { id = 1 })`.
        return PartitionClass.of(idOfCase(leaf), leaf.name(), is,
                RepresentativeSource.under(worn, new RepresentativeSource.Composed(leaf)));
    }

    private static boolean isBool(ObservedValue v, boolean expected) {
        return v instanceof ObservedValue.Bool b && b.value() == expected;
    }

    private PartitionClasses() {}
}
