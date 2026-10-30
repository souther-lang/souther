package souther.compiler.check;

import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.values.Value;

import java.util.ArrayList;
import java.util.List;

/**
 * Every value a type has, where they can be counted out at all.
 *
 * <p>Asked so that a rule saying which values a position may not hold can be read as the values it
 * may. {@code /= true} beside {@code /= false} leaves nothing where the values are two and leaves
 * almost everything where they are strings, and the whole of that difference is this answer.
 *
 * <p>Not {@link Carrier}, which answers whether a position has an order-preserving count. The two
 * questions come apart at both ends: a boolean has no order and has two values, a string has an
 * order and has no end of them. They are asked apart here as well as answered apart — nothing below
 * reads that one — so a change to which types carry an order leaves this where it was.
 *
 * <p>Exhaustive over the primitives, so one added to the language is answered here rather than
 * falling to whichever arm this happened to end with. Where the values cannot be counted out the
 * answer is nothing at all, which is what leaves a rule about them saying only what it excludes.
 */
public final class ValueUniverse {

    private ValueUniverse() {}

    /**
     * How many values of {@code type} differ, where they can be counted out and no rule holds any
     * of them back — or minus one where they cannot, which is not that there are many.
     *
     * <p>Not {@link #of}'s count as it stands. That one reads through every name a type wears to
     * the values underneath, so that a rule saying which values a position may not hold can be
     * read as the values it may: a name wrapped round a boolean is two values there whatever the
     * name's rules leave. What a reader asking how many values the type <em>has</em> needs is the
     * values the rules leave, so a count is given only where the names the type wears, and the sum
     * it is where it is one, are shown to carry no rule ({@link
     * DeclaredClauses.OnAName#carriesNone}). A rule over them leaves a count this does not read.
     */
    public static long howManyDiffer(Type type, RuleReadingContext reading) {
        RuleReadingSource source = reading.source();
        TypeView view = TypeView.of(type, source.inners(), source.symbols(), source.kinds(),
                source.sums());
        List<TypeSymbol> names = new ArrayList<>(view.wrappers());
        if (view.shape() instanceof Shape.Sum sum) {
            names.add(sum.name());
        }
        if (!DeclaredClauses.of(names, source).stream()
                .allMatch(DeclaredClauses.OnAName::carriesNone)) {
            return -1;
        }
        List<Value> every = of(type, source.inners(), source.kinds(), source.sums());
        return every == null ? -1 : every.size();
    }

    /**
     * The values of {@code type} in the order the model writes them, or null where they are not
     * something this counts out.
     *
     * <p>Read through whatever names the type wears: a name wrapped round a boolean is two values
     * like the boolean it wraps.
     */
    static List<Value> of(Type type, NewtypeInners inners, DeclarationKinds kinds, SumCases sums) {
        Type base = TypeOps.base(type, inners);
        if (base instanceof Type.Prim prim) {
            return switch (prim) {
                case BOOL -> List.of(Value.truth(false), Value.truth(true));
                // Counted out by nobody here. An `Int` and a `Date` have ends rather than a list of
                // values, and what a rule leaves between two of them is read as an interval; a
                // `String`, a `Decimal` and the rest have no end of values between any two. Both
                // are the same answer to this question, which is about writing the values down.
                case INT, DECIMAL, RATIONAL, STRING, DATE, TIME, DATETIME, INSTANT -> null;
            };
        }
        // An enumeration's cases, in the order the sum declares them. Asked of the sum directly and
        // not through {@link Carrier}: that one answers whether a position has an order-preserving
        // count, which is a different question that happens to hold of the same declarations today.
        // Read through it, a change to which types carry an order would silently change which types
        // have values that can be written out. Both take what an enumeration is from `SumCases`, so
        // this is one reading of that and not two.
        // Whether it is one is asked of its form before of what it says: a product's meaning is
        // made by reading clauses, and one being made cannot be asked.
        if (!(base instanceof Type.Ref(TypeSymbol.AtModule named) && kinds.isSum(named.key())
                && sums.of(named) instanceof SumCases.Enumeration enumeration)) {
            return null;
        }
        List<Value> values = new ArrayList<>();
        enumeration.cases().forEach(each -> values.add(Value.of(each)));
        return List.copyOf(values);
    }
}
