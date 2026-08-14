package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Whether a call written in a fixture determines one monomorphic instance of what it applies, and
 * which instance that is.
 *
 * <p>The one reading of that question. A fixture is built before there is a call to decide what a
 * declaration left open, so what a row applies has to be settled by what the row wrote — and the
 * rule is that every type variable the declaration carries is settled by the arguments, or the call
 * is refused for the variable that stayed open. A declaration being polymorphic is not the question
 * and is not an answer.
 *
 * <p>No type is worked out here. The arguments arrive already known ({@link FixtureArgumentTypes}),
 * and what this does with them is what a call does anywhere in the language: {@link TypeOps#bindVars}
 * against the declared parameter types, which is the same walk {@link CallElaborator} settles a
 * polymorphic call with. Keeping inference out is what keeps this from becoming a second reading of
 * the language's own calls.
 *
 * <p>{@link SettledCall} is the witness that the question was answered yes. It is constructed here
 * and nowhere else, so a reader holding one need not ask again — in particular, what realises the
 * call as a method ({@link FixtureCallable}) chooses a representation and decides no applicability.
 */
public final class FixtureApplication {

    private FixtureApplication() {
    }

    /** What a written call came to. */
    public sealed interface Settlement {
    }

    /** The call determines one instance, and this is it. */
    public record Settled(SettledCall call) implements Settlement {
    }

    /** A parameter the declaration gives no type, so there is nothing to settle against. */
    public record Undeclared(String parameter) implements Settlement {
    }

    /** A variable of the declaration that the written arguments left open. */
    public record Open(Type.Var variable) implements Settlement {
    }

    /** The call is written with a number of arguments the declaration does not take. */
    public record Miscalled(int written, int declared) implements Settlement {
    }

    /**
     * One monomorphic instance of a declaration, and the evidence that a fixture's call determined it.
     *
     * <p>Not a record of what was substituted: what identifies the instance is the signature it came
     * out at, read in the declaration's own order. Two calls that settle the same signature are the
     * same instance however each got there, and a name for it is a projection of that signature
     * rather than a serialisation of the bindings.
     */
    public static final class SettledCall {
        private final String reached;
        private final Hir.FnDef declaration;
        private final List<Type> params;
        private final Type result;
        private final Map<String, Type> bindings;

        private SettledCall(String reached, Hir.FnDef declaration, List<Type> params, Type result,
                            Map<String, Type> bindings) {
            this.reached = reached;
            this.declaration = declaration;
            this.params = List.copyOf(params);
            this.result = result;
            this.bindings = Map.copyOf(bindings);
        }

        /** What the row applies, under the name it reaches it by — what a report about it names. */
        public String reached() {
            return reached;
        }

        /** The declaration this is an instance of, as it was written. */
        public Hir.FnDef declaration() {
            return declaration;
        }

        /** The parameter types of this instance, in declaration order. */
        public List<Type> params() {
            return params;
        }

        /** The result type of this instance, or null where the declaration declares none. */
        public Type result() {
            return result;
        }

        /** Whether the declaration carried anything for a call to settle. */
        public boolean instantiated() {
            return !bindings.isEmpty();
        }

        /** The declaration with this instance's signature in place of the declared one. */
        public Hir.FnDef instantiatedDeclaration() {
            if (!instantiated()) {
                return declaration;
            }
            List<Hir.FnParam> settled = new ArrayList<>();
            for (Hir.FnParam p : declaration.params()) {
                settled.add(new Hir.FnParam(p.binder(), substituted(p.type()), p.typeFromPattern()));
            }
            return new Hir.FnDef(declaration.written(), declaration.declaredIn(), settled,
                    substituted(declaration.declaredReturn()), declaration.body(),
                    declaration.modifiers(), declaration.pos());
        }

        private Hir.RetType substituted(Hir.RetType t) {
            if (t == null) {
                return null;
            }
            List<Hir.TypeTerm> cases = new ArrayList<>();
            for (Hir.TypeTerm term : t.cases()) {
                cases.add(substituted(term));
            }
            return new Hir.RetType(cases, t.pos());
        }

        private Hir.TypeTerm substituted(Hir.TypeTerm term) {
            return switch (term) {
                case Hir.TypeRef r -> r.denoting(TypeOps.substitute(r.type(), bindings));
                case Hir.FnType f -> {
                    List<Hir.RetType> params = new ArrayList<>();
                    for (Hir.RetType p : f.params()) {
                        params.add(substituted(p));
                    }
                    yield new Hir.FnType(params, substituted(f.result()), f.pos());
                }
            };
        }
    }

    /**
     * What {@code declaration} comes to when applied to arguments of {@code argumentTypes}, where an
     * argument that states no type of its own is null.
     *
     * <p>A variable is settled by the arguments or it is open. Nothing is read from the position the
     * call stands at: a call's applicability is a property of the call, and taking it from the
     * surrounding row would make the same call applicable in one place and not in another. That
     * holds while a fixture expression is read on its own; a fixture that goes through elaboration is
     * what would put the question again.
     */
    public static Settlement settle(String reached, Hir.FnDef declaration,
                                    List<Type> argumentTypes, Symbols symbols) {
        List<Hir.FnParam> params = declaration.params();
        if (argumentTypes.size() != params.size()) {
            return new Miscalled(argumentTypes.size(), params.size());
        }
        List<Type> declared = new ArrayList<>();
        for (Hir.FnParam p : params) {
            if (p.type() == null) {
                return new Undeclared(p.name());
            }
            declared.add(TypeOps.resolveParamType(p.type()));
        }
        Type declaredResult = declaration.declaredReturn() == null ? null
                : TypeOps.resolveParamType(declaration.declaredReturn());
        Map<String, Type> bindings = new HashMap<>();
        for (int i = 0; i < declared.size(); i++) {
            if (argumentTypes.get(i) != null) {
                TypeOps.bindVars(declared.get(i), argumentTypes.get(i), bindings, symbols);
            }
        }
        Map<String, Type.Var> variables = new LinkedHashMap<>();
        for (Type t : declared) {
            variablesIn(t, variables);
        }
        variablesIn(declaredResult, variables);
        for (Map.Entry<String, Type.Var> variable : variables.entrySet()) {
            Type settled = bindings.get(variable.getKey());
            // NOTHING is what an empty collection binds, which is a variable no element decided.
            if (settled == null || settled == Type.NOTHING || leavesAVariable(settled)) {
                return new Open(variable.getValue());
            }
        }
        List<Type> instantiated = new ArrayList<>();
        for (Type t : declared) {
            instantiated.add(TypeOps.substitute(t, bindings));
        }
        Map<String, Type> settledOnly = new HashMap<>();
        for (String variable : variables.keySet()) {
            settledOnly.put(variable, bindings.get(variable));
        }
        return new Settled(new SettledCall(reached, declaration, instantiated,
                declaredResult == null ? null : TypeOps.substitute(declaredResult, bindings),
                settledOnly));
    }

    private static boolean leavesAVariable(Type t) {
        return Type.mentions(t, x -> x instanceof Type.Var);
    }

    private static void variablesIn(Type t, Map<String, Type.Var> out) {
        if (t == null) {
            return;
        }
        if (t instanceof Type.Var v) {
            out.putIfAbsent(v.name(), v);
        }
        Type.forEachChild(t, held -> variablesIn(held, out));
    }
}
