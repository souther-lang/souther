package souther.compiler.execute;

import souther.compiler.diag.SourcePos;
import souther.compiler.types.TypeSymbol;

import java.util.List;
import java.util.Optional;

/**
 * A newtype construction whose argument is a constant, and everything deciding it needs.
 *
 * <p>A closed question. Whether {@code 金額(500)} satisfies what {@code 金額} is declared to hold of
 * its values is answered by running the check the language already has for it, and nothing else
 * about the module has to be read to ask that. What used to happen — the constant was run, and then
 * the module's declaration was read a second time to find out which clause it was that failed — put
 * the compiler's own query graph inside the thing doing the running. The clauses come with the
 * question instead.
 *
 * @param writtenIn the module the construction is written in, which is the compile whose classes
 *                  this is resolved against. Not the same as the module that declares the type: a
 *                  construction may name an imported one, and both have to be reachable.
 * @param typeName  the type as it was written, which is what a message about it quotes
 * @param type      which module declared the type, so the check that runs is that module's
 * @param value     the constant the construction was handed
 * @param clauses   what the type is declared to hold of its values, in declaration order
 * @param pos       where the construction is written
 */
public record ConstantConstruction(String writtenIn, String typeName, TypeSymbol.AtModule type,
                                   WrittenValue value, List<Clause> clauses, SourcePos pos) {

    public ConstantConstruction {
        clauses = List.copyOf(clauses);
    }

    /**
     * One clause of the invariant, at the place it is declared.
     *
     * <p>Its place in {@link #clauses} is the clause's declaration order, which is what the check
     * for it is keyed by, and the order is why a violation names the clause a construction would
     * have named: the clauses are asked one at a time in the order they are written, and the first
     * that does not hold is the one reported.
     *
     * <p>The name is what a report quotes and a clause need not carry one. A clause with no name
     * still holds or fails; what a reader is told is then that the invariant was violated rather
     * than which part of it.
     */
    public record Clause(Optional<String> name) {

        public Clause {
            if (name == null) {
                throw new IllegalArgumentException("a clause either carries a name or does not");
            }
        }
    }
}
