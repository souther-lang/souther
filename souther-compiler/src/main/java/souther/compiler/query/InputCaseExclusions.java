package souther.compiler.query;

import souther.compiler.ast.Hir;
import souther.compiler.inputs.Admits;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.TermPath;
import souther.compiler.types.TypeSymbol;

import java.util.LinkedHashSet;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Which of the cases declared at an input position no row can be written at.
 *
 * <p>The one thing a count of what the rows cover takes from a reading of the input, asked here so
 * that the count itself never holds one. A measure handed the reading would need one for a
 * behavior that has no reading to be handed — and what it would be given is an input with no
 * positions, which answers "nothing is refused" while saying it read something.
 *
 * <p>Only a refusal takes a case out. A case the reading could not settle stays counted, because
 * what takes it out is a proof and not the absence of one.
 */
public sealed interface InputCaseExclusions {

    /**
     * The cases at {@code position} the rules refuse, out of the ones {@code declared} there.
     *
     * @param position which input position, counted as the signature declares them
     * @param declared the cases that position's type has, which is what these are taken out of
     */
    Set<TypeSymbol> at(int position, Set<TypeSymbol> declared);

    /** What the rules of one behavior's own input refuse, read off the reading of it. */
    static InputCaseExclusions of(InputForMeasurement input) {
        return switch (input) {
            case InputForMeasurement.Local(Hir.SpecBehavior spec, InputDomain read) ->
                    new AsTheRulesRefuse(spec, read);
            // A composition has no positions of its own to refuse anything at: what it takes is its
            // first stage's, and a case refused there is refused where that stage is measured.
            case InputForMeasurement.AtStages _ -> NothingIsRefusedHere.INSTANCE;
        };
    }

    /**
     * Read off the reading, case by case and by the declaration each case is.
     *
     * <p>Which position a case is asked about is the parameter's name, which is how the reading
     * files what it read. The two come from one declaration, so there is no pairing to get wrong.
     */
    record AsTheRulesRefuse(Hir.SpecBehavior spec, InputDomain read) implements InputCaseExclusions {

        @Override
        public Set<TypeSymbol> at(int position, Set<TypeSymbol> declared) {
            // Counted as the signature lists them, and named as the declaration writes them, which
            // are two lists that need not be the same length. A position past the names has none
            // to ask the reading about, and nothing is proven about a position nobody asked about.
            if (declared.isEmpty() || position >= spec.params().size()) {
                return Set.of();
            }
            Position stands = read.at(TermPath.of(spec.params().get(position).name()));
            if (stands == null) {
                return Set.of();   // nothing was read about the position, so nothing is proven of it
            }
            return declared.stream()
                    .filter(each -> stands.admissionOf(each) instanceof Admits.Refused)
                    .collect(Collectors.toCollection(LinkedHashSet::new));
        }
    }

    /** No case is refused, because there are no rules here to refuse one. */
    enum NothingIsRefusedHere implements InputCaseExclusions {

        INSTANCE;

        @Override
        public Set<TypeSymbol> at(int position, Set<TypeSymbol> declared) {
            return Set.of();
        }
    }
}
