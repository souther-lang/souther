package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.List;

/**
 * The conjuncts of the rules written on a type, in the order the author wrote them.
 *
 * <p>Every name the value wears, not the outermost one. A rule written on the type a newtype wraps
 * bounds the value as much as one written on the newtype does, and the two are read together:
 * {@code Inner: value >= 0} under {@code Outer: value <= 10} is a range of {@code [0, 10]}, and
 * neither layer alone says so. How far that reaches is asked of {@link TypeOps} rather than walked
 * again here.
 *
 * <p>Walked once, because the number a conjunct carries is part of an identity. A line is named by
 * the clause and the conjunct it came out of ({@link DeclaredBounds.Drawn}), counted over every
 * conjunct and not over the ones something came of — so a reading that makes nothing of one
 * conjunct still numbers the next as a reading that makes something of it does. A second walk with
 * its own counter would call one authored line two the day the two disagreed about which conjuncts
 * there are.
 *
 * <p>Nothing is read out of a conjunct here. Which number a side of one names is
 * {@link ClauseSubject}'s and where it leaves the values is {@link InvariantBound}'s, and both are
 * projections of the same text rather than steps of one reading. What a conjunct is <em>about</em>
 * is neither of those: it is the canonical quantity its arithmetic came to, which the reading that
 * turns clauses into constraints works out ({@link FieldDomains#writtenAbout}).
 */
public final class DeclaredClauses {

    /**
     * One conjunct of one rule of a declaration.
     *
     * @param rule     the clause it is a conjunct of, as a report names it
     * @param conjunct which of that clause's conjuncts it is, counted from zero over all of them
     * @param expr     the conjunct itself
     */
    public record Conjunct(RuleRef.Invariant rule, int conjunct, Hir.Expr expr) {

        public Conjunct {
            if (rule == null || expr == null) {
                throw new IllegalArgumentException("a conjunct is some clause's text");
            }
            if (conjunct < 0) {
                throw new IllegalArgumentException(
                        "a conjunct of a clause is counted from zero: " + conjunct);
            }
        }
    }

    /** Every conjunct of every rule written on {@code type} and on the types it wraps. */
    public static List<Conjunct> of(Type type, Symbols symbols) {
        List<Conjunct> out = new ArrayList<>();
        for (TypeOps.Layer layer : TypeOps.newtypeChain(type, symbols)) {
            // A layer wraps a declaration a module wrote, which is what having a `Hir.Data` for it
            // says; the pattern is where the layer's name says so.
            if (!(layer.named() instanceof TypeSymbol.AtModule named)) {
                continue;
            }
            // The clauses with the declaration each was written on, which is what names the line
            // (ADR-0090). Read flat, every clause a spread brought in was named after the type that
            // spread it, and two clauses of one declaration were one rule.
            for (TypeOps.Declared declared
                    : TypeOps.declaredInvariants(named, layer.data(), symbols, _ -> null)) {
                RuleRef.Invariant rule = new RuleRef.Invariant(Clause.Ref.of(declared));
                int conjunct = -1;
                for (Hir.Expr each : ClauseHelpers.conjunctsOf(declared.clause().expr())) {
                    conjunct++;
                    out.add(new Conjunct(rule, conjunct, each));
                }
            }
        }
        return List.copyOf(out);
    }

    private DeclaredClauses() {}
}
