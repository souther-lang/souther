package souther.compiler.partition;

import souther.compiler.ast.Ast;
import souther.compiler.check.Shape;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.check.TypeView;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;
import souther.compiler.types.TypeReachName;

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
        // The same names twice over, because two different questions are asked of them. Whether an
        // observed value is under this class is asked of the declarations, and what a row writes it
        // under is asked of the module doing the writing — one of these is an identity and the other
        // is a reference, and a module reaching a name through an alias answers them differently.
        List<TypeReachName.Written> writes = new ArrayList<>();
        for (TypeName each : worn) {
            if (!(symbols.reach(each) instanceof TypeReachName.Written written)) {
                // A name the position wears that nothing here writes. The classes are still the
                // position's, and no row for any of them can be written down, so each says that
                // rather than being offered a value spelled with a name that resolves to nothing.
                return unwritable(view, symbols, worn, each);
            }
            writes.add(written);
        }
        return switch (view.shape()) {
            // A `Bool` is two values. No other primitive has classes to read off its type: what a
            // number's rules leave is a range with edges — everything outside a newtype's invariant
            // is refused at construction (E1903), so there is no class on the other side to cover —
            // and what does divide a number is a threshold, which is read from a body and not here.
            case Shape.Scalar scalar -> scalar.prim() == Type.Prim.BOOL
                    ? eitherWay(worn, writes) : List.of();
            case Shape.Sum sum -> caseClasses(Type.ref(sum.name()), worn, writes, symbols);
            case Shape.Cases cases -> caseClasses(Type.union(cases.members()), worn, writes, symbols);
            case Shape.Optional optional -> heldOrNot(optional.element(), worn, writes, symbols);
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

    /**
     * The classes of a position whose values cannot be written here at all, each saying why.
     *
     * <p>They are counted like any other: a case a module does not expose is still a case of the
     * position, and a row already sitting in one still covers it. What is absent is the offer of a
     * new row, and the reason is the model's — {@code domain} keeps the case to itself — rather than
     * anything about this generator.
     */
    private static List<PartitionClass> unwritable(TypeView view, Symbols symbols,
                                                   List<TypeName> worn, TypeName unnamed) {
        String why = notExposed(unnamed);
        List<PartitionClass> out = new ArrayList<>();
        // The classes of the same position with no names to write them under. What each is and what
        // reads a value into it are the position's either way; only the recipes are dropped, and
        // they are what there is no writing them.
        for (PartitionClass each : of(new TypeView(view.declared(), List.of(), view.shape()),
                symbols)) {
            out.add(PartitionClass.ungeneratable(each.id(), each.label(),
                    Classifier.under(worn, each.classifier()), why));
        }
        return out;
    }

    /** Why nothing here can write a value of {@code unnamed}: no spelling reaches it. */
    private static String notExposed(TypeName unnamed) {
        return "`" + unnamed.module() + "` does not expose `" + unnamed.name()
                + "`, so nothing here can name it";
    }

    /** The two values of a {@code Bool}, under the names the position writes them under. */
    private static List<PartitionClass> eitherWay(List<TypeName> worn,
                                                  List<TypeReachName.Written> writes) {
        return List.of(
                PartitionClass.of("true", "true",
                        Classifier.under(worn, Classifier.byShape(v -> isBool(v, true))),
                        RepresentativeSource.under(writes,
                                RepresentativeSource.of(FixtureTemplate.bool(true)))),
                PartitionClass.of("false", "false",
                        Classifier.under(worn, Classifier.byShape(v -> isBool(v, false))),
                        RepresentativeSource.under(writes,
                                RepresentativeSource.of(FixtureTemplate.bool(false)))));
    }

    /** Whether an optional holds anything, which is the one division its type makes. */
    private static List<PartitionClass> heldOrNot(Type element, List<TypeName> worn,
                                                  List<TypeReachName.Written> writes,
                                                  Symbols symbols) {
        List<FixtureTemplate> some = Partitions.representativesOf(element, symbols);
        return List.of(
                PartitionClass.of("None", "None",
                        Classifier.under(worn,
                                Classifier.byShape(v -> v instanceof ObservedValue.Absent)),
                        RepresentativeSource.under(writes,
                                RepresentativeSource.of(FixtureTemplate.none()))),
                some.isEmpty()
                        ? PartitionClass.ungeneratable("Some", "Some",
                                Classifier.under(worn, Classifier.byShape(
                                        v -> !(v instanceof ObservedValue.Absent))),
                                "nothing here composed a value of " + Type.show(element))
                        : PartitionClass.of("Some", "Some",
                                Classifier.under(worn, Classifier.byShape(
                                        v -> !(v instanceof ObservedValue.Absent))),
                                RepresentativeSource.under(writes,
                                        RepresentativeSource.of(some))));
    }

    /** A sum's cases, each a class, under the names the position writes them under. */
    private static List<PartitionClass> caseClasses(Type sum, List<TypeName> worn,
                                                    List<TypeReachName.Written> writes,
                                                    Symbols symbols) {
        List<PartitionClass> cases = new ArrayList<>();
        for (TypeName leaf : TypeOps.leafCases(sum, symbols)) {
            cases.add(caseClass(leaf, worn, writes, symbols));
        }
        return cases;
    }

    /** What a case's class is called, in one place: a reading that decides which cases the position
     *  holds names the same classes the reading above builds. */
    static String idOfCase(TypeName leaf) {
        return leaf.name();
    }

    private static PartitionClass caseClass(TypeName leaf, List<TypeName> worn,
                                            List<TypeReachName.Written> writes, Symbols symbols) {
        Classifier is = Classifier.under(worn, Classifier.byShape(v -> switch (v) {
            case ObservedValue.Unit u -> leaf.equals(u.type());
            case ObservedValue.Constructed c -> leaf.equals(c.type());
            default -> false;
        }));
        // A case whose module does not expose it: a value of the position all the same, and one no
        // author here can write down. Said as that, rather than offered under a spelling that
        // resolves to nothing wherever the row is pasted (issue #696).
        if (!(symbols.reach(leaf) instanceof TypeReachName.Written names)) {
            return PartitionClass.ungeneratable(idOfCase(leaf), leaf.name(), is, notExposed(leaf));
        }
        if (!(symbols.get(leaf) instanceof Ast.Data data)) {
            return PartitionClass.of(idOfCase(leaf), leaf.name(), is,   // naming it builds it
                    RepresentativeSource.under(writes,
                            RepresentativeSource.of(FixtureTemplate.unitCase(names))));
        }
        if (data.newtype()) {
            List<FixtureTemplate> inner = Partitions.insideTheNewtype(leaf, symbols);
            return inner.isEmpty()
                    ? PartitionClass.ungeneratable(idOfCase(leaf), leaf.name(), is,
                            "nothing here composed a value of what `" + leaf.name() + "` wraps")
                    : PartitionClass.of(idOfCase(leaf), leaf.name(), is,
                            RepresentativeSource.under(writes, RepresentativeSource.under(
                                    List.of(names), RepresentativeSource.of(inner))));
        }
        // A record case is written field by field, which is the generator's composition. So the class
        // names the constructor and the generator does the composing — the same walk every other
        // record goes through, rules between the fields and all. Under the position's names either
        // way: what is composed is an `Approved`, and what the row writes is `DecisionN(Approved
        // { id = 1 })`.
        return PartitionClass.of(idOfCase(leaf), leaf.name(), is,
                RepresentativeSource.under(writes, new RepresentativeSource.Composed(leaf)));
    }

    private static boolean isBool(ObservedValue v, boolean expected) {
        return v instanceof ObservedValue.Bool b && b.value() == expected;
    }

    private PartitionClasses() {}
}
