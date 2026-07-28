package souther.compiler.check;

import souther.compiler.ast.Ast;

import java.util.Map;

/**
 * What stays fixed while one definition is checked: the module's symbol table, the {@code data} an
 * invariant or a codec is written against, and the injected behaviors a body may call.
 *
 * <p>None of the three changes as the walk descends into an expression, so they travel together
 * rather than as three parameters threaded through every method. What does change — the variable
 * environment and the expected type pushed down from the surrounding context — is passed separately.
 */
public record CheckContext(Symbols symbols, Ast.Data data, Map<String, ReqSig> reqs,
                           Map<String, ReqSig> callees) {

    /** A context with no behavior callable by name — every construction that predates the
     *  distinction, and every position where only injected behaviors are in sight. */
    public CheckContext(Symbols symbols, Ast.Data data, Map<String, ReqSig> reqs) {
        this(symbols, data, reqs, Map.of());
    }

    /** No {@code data} in scope and no behaviors — the context an invariant-free, injection-free
     *  expression is checked in. */
    public static CheckContext of(Symbols symbols) {
        return new CheckContext(symbols, null, Map.of(), Map.of());
    }

    /** The same context checking a different {@code data}'s invariant, decoder, or encoder. */
    public CheckContext forData(Ast.Data other) {
        return new CheckContext(symbols, other, reqs, callees);
    }

    /** The same context with the behaviors a body may call in scope. */
    public CheckContext withReqs(Map<String, ReqSig> required) {
        return new CheckContext(symbols, data, required, callees);
    }

    /** The same context with the behaviors a body may call by name in scope — the ones that require
     *  nothing (spec {@code [#calling-a-behavior]}). */
    public CheckContext withCallees(Map<String, ReqSig> callable) {
        return new CheckContext(symbols, data, reqs, callable);
    }
}
