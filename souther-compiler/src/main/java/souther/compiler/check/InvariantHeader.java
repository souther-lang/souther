package souther.compiler.check;

import souther.compiler.diag.SourcePos;

import java.util.Optional;

/**
 * What a rule that governs a declaration is called, and where its author wrote it.
 *
 * <p>A clause without what it states. The name and the position are what every representation of a
 * declaration agrees on: resolution settles which clauses there are, what each is called and where
 * it stands, and the only thing that makes one afterwards is
 * {@link souther.compiler.ast.Hir.InvariantClause#with}, which replaces the expression and carries
 * the name and the position across. Nothing below adds a clause, drops one, or moves one. So a
 * reader that wants these can read them off whichever representation it is holding, and a reader
 * that wants what the clause states cannot — which is why the expression is not here.
 *
 * <p>Held to those two. Which declaration a rule was written on, and which of that declaration's
 * rules it is, are answered by {@link TypeOps.Declared} for the readers that ask; put here they
 * would be two more things every representation had to agree about for no reader that asks.
 *
 * @param name  what the author called the rule, or nothing where they wrote none
 * @param pos   where the clause was written
 */
public record InvariantHeader(Optional<String> name, SourcePos pos) {

    public InvariantHeader {
        if (name == null || pos == null) {
            throw new IllegalArgumentException("a rule has a name it may not have been given, and a"
                    + " place it was written");
        }
    }
}
