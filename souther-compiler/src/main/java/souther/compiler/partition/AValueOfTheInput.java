package souther.compiler.partition;

import souther.compiler.check.ExpandedClauseResult;
import souther.compiler.check.RuleReadingSource;
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
 * reaches writes a clause, and none is a sum, whose value is one of its cases. Every other type a
 * place of it holds then has a value whatever the others hold — a number of its kind, a collection
 * holding nothing, nothing in an option, a record of such values — so a value holding any whole
 * numbers at places that are fields of fields of a parameter is written by putting each where it
 * is asked and anything at the rest. A place inside a container is not one of those: a container
 * is written holding nothing.
 *
 * <p>Not shown is not that none exists. A clause, a case or a place inside an element asks more of
 * the declarations than is read here, and a value may well exist there.
 */
final class AValueOfTheInput {

    private AValueOfTheInput() {}

    /**
     * Whether a value of the input {@code read} reads exists holding any whole number at each of
     * {@code places}: every position of the input is of a type that states nothing of its values,
     * and each place is a whole number reached from a parameter through fields alone.
     */
    static boolean holdsAnyWholeNumbersAt(InputReading read, Collection<TermPath> places) {
        InputDomain domain = read.domain();
        for (Position each : domain.positions()) {
            if (!statesNothing(each.type(), read.rules())) {
                return false;
            }
        }
        for (TermPath place : places) {
            Position at = domain.at(place);
            if (at == null || at.type() != Type.INT || !place.steps().stream()
                    .allMatch(TermPath.Step.Field.class::isInstance)) {
                return false;
            }
        }
        return true;
    }

    /** Whether {@code type} has a value whatever is asked of the others, as the declarations
     *  write it: no clause and no case of its own. */
    private static boolean statesNothing(Type type, RuleReadingSource rules) {
        return switch (type) {
            case Type.Prim _, Type.ListOf _, Type.SetOf _, Type.MapOf _, Type.OptionOf _ -> true;
            case Type.TupleOf tuple -> tuple.elements().stream()
                    .allMatch(each -> statesNothing(each, rules));
            case Type.Ref(TypeSymbol.AtModule declared) -> rules.sums().of(declared) == null
                    && rules.invariants().of(declared.key())
                            instanceof ExpandedClauseResult.Found(var clauses)
                    && clauses.clauses().isEmpty();
            default -> false;
        };
    }
}
