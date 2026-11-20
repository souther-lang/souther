package souther.compiler.partition;

import souther.compiler.check.ExpandedClauseResult;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.Shape;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.TermPath;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.Collection;

/**
 * Whether a value of a behavior's input exists holding whatever whole numbers are asked of some of
 * its places, shown from the declarations of its types and from nothing a search found.
 *
 * <p>Shown only where no type of the input states anything of its values: no declaration it
 * reaches, nor any name a value of it wears, writes a clause, and none is a sum, whose value is one
 * of its cases. Every other type a place of it holds then has a value whatever the others hold — a
 * number of its kind, a collection holding nothing, nothing in an option, a record of such values
 * — so a value holding any whole numbers at places that are fields of fields of a parameter is
 * written by putting each where it is asked and anything at the rest. A place inside a container is
 * not one of those: a container is written holding nothing.
 *
 * <p>Not shown is not that none exists. A clause, a case or a place inside an element asks more of
 * the declarations than is read here, and a value may well exist there.
 *
 * <p>What a type is, is asked of its view ({@link TypeView}), which says the names a value wears
 * and what it is under them.
 */
final class AValueOfTheInput {

    private AValueOfTheInput() {}

    /**
     * Whether a value of the input {@code read} reads exists holding any whole number at each of
     * {@code places}: every position of the input is of a type that states nothing of its values,
     * and each place is a whole number wearing no name, reached from a parameter through fields
     * alone.
     */
    static boolean holdsAnyWholeNumbersAt(InputReading read, Collection<TermPath> places) {
        InputDomain domain = read.domain();
        RuleReadingSource rules = read.rules();
        for (Position each : domain.positions()) {
            if (!statesNothing(viewOf(each.type(), rules), rules)) {
                return false;
            }
        }
        for (TermPath place : places) {
            Position at = domain.at(place);
            if (at == null || !place.steps().stream()
                    .allMatch(TermPath.Step.Field.class::isInstance)) {
                return false;
            }
            TypeView view = viewOf(at.type(), rules);
            if (!view.wrappers().isEmpty()
                    || !(view.shape() instanceof Shape.Scalar(Type.Prim prim))
                    || prim != Type.Prim.INT) {
                return false;
            }
        }
        return true;
    }

    private static TypeView viewOf(Type type, RuleReadingSource rules) {
        return TypeView.of(type, rules.inners(), rules.symbols(), rules.kinds(), rules.sums());
    }

    /** Whether a value of {@code view} exists whatever is asked of the others, as the
     *  declarations write it: no clause on any name it wears or on its record, and no case. */
    private static boolean statesNothing(TypeView view, RuleReadingSource rules) {
        if (!view.wrappers().stream().allMatch(name -> writesNoClause(name, rules))) {
            return false;
        }
        return switch (view.shape()) {
            case Shape.Scalar _, Shape.Container _, Shape.Optional _ -> true;
            case Shape.Product product -> writesNoClause(product.name(), rules);
            case Shape.Unit unit -> writesNoClause(unit.name(), rules);
            case Shape.Tuple tuple -> tuple.elements().stream()
                    .allMatch(each -> statesNothing(viewOf(each, rules), rules));
            default -> false;
        };
    }

    /** Whether the declaration {@code name} writes no clause, as the reading of its clauses
     *  found them. */
    private static boolean writesNoClause(TypeSymbol name, RuleReadingSource rules) {
        return name instanceof TypeSymbol.AtModule declared
                && rules.invariants().of(declared.key())
                        instanceof ExpandedClauseResult.Found(var clauses)
                && clauses.clauses().isEmpty();
    }
}
