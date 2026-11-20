package souther.compiler.partition;

import souther.compiler.check.DeclarationMeaning;
import souther.compiler.check.DeclaredBounds;
import souther.compiler.check.FieldDomains;
import souther.compiler.check.PublishedDeclarationResult;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.Shape;
import souther.compiler.check.SumCases;
import souther.compiler.check.TypeOps;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.RuleAddress;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * Whether a value of a behavior's input exists holding whatever whole numbers are asked of some of
 * its places, and what those numbers have to meet for it to: shown from the declarations of its
 * types, as their owners read them, and from nothing a search found.
 *
 * <p>The input is walked from each parameter down the fields to each place asked of. A record the
 * walk goes through writes no clause, so that nothing ties a place to what stands beside it. A
 * place holds a number, a date or a case of an enumeration; one wearing a name holds the numbers the
 * rules of its names leave it ({@link DeclaredBounds#wholeRunOf}), every one of which is a value,
 * and those are what is asked of it. Every other part of the input holds whatever value of its type
 * is shown to exist ({@link #aValueIsShownToExist}), which nothing asked of the places turns on.
 *
 * <p>Not shown is not that none exists. A clause tying fields together, a place inside an element
 * or a case, or a name whose rules leave holes asks more of the declarations than is read here, and
 * a value may well exist there.
 */
final class AValueOfTheInput {

    private AValueOfTheInput() {}

    /**
     * What a value of the input {@code read} reads has to meet at {@code places} to exist holding
     * any whole number at each within that and within the ends of what the place holds — every one
     * of which is then a value — or nothing where that is not shown. An {@code Int} holds every whole
     * number between its ends, which a caller keeps a value within, and a {@code Decimal} is any
     * finite decimal number, which every whole number is. A date is the count of its days, and
     * every count between the calendar's first day and its last is a day there is; a case of an
     * enumeration is where it stands on the order its cases are declared in, and every place on
     * that order is a case.
     */
    static Optional<List<TakenConstraint.Affine>> whatAValueAtThemMeets(InputReading read,
                                                                       Collection<TermPath> places) {
        Optional<Map<TermPath, WholeRun>> runs = runsAt(read, places);
        if (runs.isEmpty()) {
            return Optional.empty();
        }
        List<TakenConstraint.Affine> out = new ArrayList<>();
        runs.get().forEach((place, run) -> {
            NumericTerm number = new NumericTerm.ValueOf(place);
            if (run.least() != null) {
                out.add(new TakenConstraint.Affine(LinearForm.atomMinusConstant(number,
                        ExactRatio.of(run.least())), Rel.GE));
            }
            if (run.greatest() != null) {
                out.add(new TakenConstraint.Affine(LinearForm.atomMinusConstant(number,
                        ExactRatio.of(run.greatest())), Rel.LE));
            }
        });
        return Optional.of(List.copyOf(out));
    }

    /**
     * The whole numbers a value of the input {@code read} reads holds at {@code place}, every one
     * of which some value holds there, what the rest of it holds aside ({@link #whatAValueAtThemMeets}
     * of the one place): within the ends of what the place holds, and within those this says,
     * each none where there is none. Nothing where that is not shown.
     */
    static Optional<WholeRun> wholeNumbersAt(InputReading read, TermPath place) {
        return runsAt(read, List.of(place)).map(runs -> runs.get(place));
    }

    /**
     * The least and greatest whole number of a run, every one between them in it: each null where
     * the run has no end there beside what the place holds.
     */
    record WholeRun(BigInteger least, BigInteger greatest) {

        static final WholeRun OPEN = new WholeRun(null, null);
    }

    /** What {@code places} each hold, as the walk of the input finds it, or nothing where a value
     *  holding any whole number within that at each is not shown. */
    private static Optional<Map<TermPath, WholeRun>> runsAt(InputReading read,
                                                            Collection<TermPath> places) {
        Map<TermPath, WholeRun> out = new LinkedHashMap<>();
        Set<TermPath> asked = Set.copyOf(places);
        for (InputDomain.Parameter each : read.domain().parameters()) {
            if (walk(TermPath.of(each.name()), each.type(), asked, read, out) < 0) {
                return Optional.empty();
            }
        }
        return out.size() == asked.size() ? Optional.of(out) : Optional.empty();
    }

    /**
     * The walk of the part at {@code at}, of {@code type}: how many of {@code places} it found
     * there, what each holds put on {@code out}, or -1 where no value is shown.
     */
    private static int walk(TermPath at, Type type, Set<TermPath> places, InputReading read,
                            Map<TermPath, WholeRun> out) {
        RuleReadingSource rules = read.rules();
        TypeView view = TypeView.of(type, rules.inners(), rules.symbols(), rules.kinds(),
                rules.sums());
        if (places.contains(at)) {
            WholeRun run = held(view, read);
            if (run == null) {
                return -1;
            }
            out.put(at, run);
            return 1;
        }
        boolean onTheWay = places.stream().anyMatch(place -> place.steps().size()
                > at.steps().size() && place.prefix(at.steps().size()).equals(at));
        if (!onTheWay) {
            return aValueIsShownToExist(type, read) ? 0 : -1;
        }
        if (!view.wrappers().stream().allMatch(name -> writesNoClause(name, rules))
                || !(view.shape() instanceof Shape.Product product)) {
            return -1;
        }
        if (!writesNoClause(product.name(), rules)) {
            return heldBesideItsClauses(at, product, places, read, out) ? 1 : -1;
        }
        int found = 0;
        for (Map.Entry<String, Type> field : product.fields().entrySet()) {
            int here = walk(at.then(field.getKey()), field.getValue(), places, read, out);
            if (here < 0) {
                return -1;
            }
            found += here;
        }
        return found;
    }

    /**
     * Whether a value of the record {@code product} at {@code at}, whose declaration writes a
     * clause, holds any whole number of a run at the one place of {@code places} below it, put on
     * {@code out}: the place a field of it holding a number, and the run the one its rules leave
     * the field, every number of which is that field of some value they all hold of
     * ({@link DeclaredBounds#wholeRunAt}), as they call it ({@link RuleAddress#of}). Not
     * shown where two places are asked below it,
     * which a run of each alone says nothing of together.
     */
    private static boolean heldBesideItsClauses(TermPath at, Shape.Product product,
                                                Set<TermPath> places, InputReading read,
                                                Map<TermPath, WholeRun> out) {
        List<TermPath> below = places.stream().filter(place -> place.steps().size()
                > at.steps().size() && place.prefix(at.steps().size()).equals(at)).toList();
        if (below.size() != 1 || below.getFirst().steps().size() != at.steps().size() + 1
                || !(below.getFirst().steps().getLast() instanceof TermPath.Step.Field(String f))
                || !(product.name() instanceof TypeSymbol.AtModule record)
                || !(product.fields().get(f) instanceof Type.Prim prim)
                || (prim != Type.Prim.INT && prim != Type.Prim.DECIMAL)) {
            return false;
        }
        RuleAddress named = RuleAddress.of(at, below.getFirst());
        WholeRun run = named == null ? null
                : wholeOf(DeclaredBounds.wholeRunAt(record, named.key(), read.ruleReading()));
        if (run == null) {
            return false;
        }
        out.put(below.getFirst(), run);
        return true;
    }

    /** The whole numbers of {@code run}, every one between its least and greatest, or null where
     *  it is none, holds none, or an end names no number. */
    private static WholeRun wholeOf(NumericDomain.Bounds run) {
        if (run == null || !run.holdsAValue()) {
            return null;
        }
        BigInteger least = run.min() == null ? null : run.min().wholeAdmitted(true);
        BigInteger greatest = run.max() == null ? null : run.max().wholeAdmitted(false);
        if ((run.min() != null && least == null) || (run.max() != null && greatest == null)
                || (least != null && greatest != null && least.compareTo(greatest) > 0)) {
            return null;
        }
        return new WholeRun(least, greatest);
    }

    /**
     * What a place of {@code view} holds: any whole number, where it is a number, a date or a case
     * of an enumeration wearing no name that writes a clause; the whole numbers of the run a number
     * wearing names that do is
     * left by their rules, every number of which they leave it; and null for anything else, or a
     * run holding no whole number.
     */
    private static WholeRun held(TypeView view, InputReading read) {
        boolean aNumber = view.shape() instanceof Shape.Scalar(Type.Prim prim)
                && (prim == Type.Prim.INT || prim == Type.Prim.DECIMAL);
        boolean aDate = view.shape() instanceof Shape.Scalar(Type.Prim prim)
                && prim == Type.Prim.DATE;
        if (view.wrappers().stream().allMatch(name -> writesNoClause(name, read.rules()))) {
            return (aNumber || aDate || anEnumeration(view)) ? WholeRun.OPEN : null;
        }
        return aNumber ? wholeOf(DeclaredBounds.wholeRunOf(view, read.ruleReading())) : null;
    }

    /**
     * Whether some value of {@code type} is shown to exist: one no rule of its own is written on —
     * a number, a string, a time, a container, which may hold nothing, an option, which may be
     * none — or a declaration whose rules are shown to leave it one
     * ({@link FieldDomains#shownToHoldAValue}), the name it is written under and the record it
     * names alike; or a sum some case of which is.
     */
    static boolean aValueIsShownToExist(Type type, InputReading read) {
        if (type == null) {
            return false;
        }
        RuleReadingSource rules = read.rules();
        if (TypeOps.outermost(type, rules.inners()) instanceof TypeOps.Unwrapped worn
                && worn.layer().named() instanceof TypeSymbol.AtModule name
                && !FieldDomains.of(name, read.ruleReading()).shownToHoldAValue()) {
            return false;
        }
        return switch (TypeView.shapeOf(type, rules.inners(), rules.symbols(), rules.kinds(),
                rules.sums())) {
            case Shape.Scalar _, Shape.Unit _, Shape.Sequence _, Shape.Mapping _,
                 Shape.Optional _ -> true;
            case Shape.Product(TypeSymbol.AtModule record, var _) ->
                    FieldDomains.of(record, read.ruleReading()).shownToHoldAValue();
            // A sum holds a value where a case of it does and nothing of its own rules the value
            // out: the case is a value of the sum.
            case Shape.Sum(var _, SumCases.Cases reaches, var _) ->
                    reaches.cases().stream().anyMatch(each ->
                            each instanceof TypeSymbol.AtModule member
                            && aValueIsShownToExist(Type.ref(member), read));
            case null, default -> false;
        };
    }

    /** Whether {@code view} is an enumeration: a sum every case of which is a unit, sharing
     *  nothing, so a value of it is which case it is and nothing a clause can state. */
    private static boolean anEnumeration(TypeView view) {
        return view.shape() instanceof Shape.Sum sum
                && sum.reaches() instanceof SumCases.Enumeration
                && sum.common() instanceof Shape.CommonProduct.None;
    }

    /** Whether the declaration {@code name} writes no clause and spreads nothing, as it publishes
     *  what it says: a unit, or a product of its own fields alone. */
    private static boolean writesNoClause(TypeSymbol name, RuleReadingSource rules) {
        if (!(name instanceof TypeSymbol.AtModule declared)
                || !(rules.published().of(declared.key())
                        instanceof PublishedDeclarationResult.Found(DeclarationMeaning said))) {
            return false;
        }
        return switch (said) {
            case DeclarationMeaning.Product product ->
                    product.clauses().isEmpty() && product.includes().isEmpty();
            case DeclarationMeaning.Unit _ -> true;
            case DeclarationMeaning.Sum _ -> false;
        };
    }
}
