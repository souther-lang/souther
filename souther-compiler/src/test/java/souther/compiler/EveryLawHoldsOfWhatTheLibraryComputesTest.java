package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.check.BoundOperationFacts;
import souther.compiler.check.DeclaredArgument;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Every law the library's operations are settled by holds of what the library computes, over
 * values chosen at the edges each law turns on.
 *
 * <p>A law is an equivalence a reader carries a statement across, and the binder holds it to the
 * signature only: that each argument it names is there and has the side it is observed on. Whether
 * the answer really comes out that way is what the operation's definition says, and this asks the
 * definition. What is checked is written from the law itself — the observation of the answer on one
 * side, the law's proposition over the same arguments on the other — so no law is declared or
 * derived without being run, and none is run in words of its own.
 *
 * <p>A run over finitely many values, which is evidence and not a proof: the values are the edges a
 * law turns on — a count below nought, at nought, at and past the end; a container empty, holding
 * one, holding a value twice; a closure true of every element, of none, of some; a string empty,
 * blank, and widening under a case mapping. A law says nothing of a call that stops on its
 * arguments, so a call that stops is not held to it, and every law is still held to one that does
 * not.
 */
class EveryLawHoldsOfWhatTheLibraryComputesTest {

    /** One check of one law: the values its arguments are written as, and the law it is held to. */
    private record Check(String operation, OperationLaw.Observed observed, List<String> arguments,
                         String holds) {}

    @Test
    void everyLawHoldsWhereItsOperationAnswers() throws Exception {
        List<List<Check>> byLaw = new ArrayList<>();
        DefaultBoundOperationFacts.get().settled().forEach((operation, settled) ->
                settled.forEach((observed, settling) -> {
                    if (settling instanceof BoundOperationFacts.Settled.ByALaw(var law, var _)) {
                        byLaw.add(checksOf((ValueName.Stdlib.Operation) operation, law));
                    }
                }));
        StringBuilder module = new StringBuilder("""
                module demo

                data In = { k: Int }
                data Out = { holds: Bool }
                """);
        for (int at = 0; at < byLaw.size(); at++) {
            module.append("\nbehavior law").append(at).append(" : (i: In) -> Out constructs Out\n")
                    .append("let law").append(at).append(" (i) = Out { holds = ")
                    .append(chosen(byLaw.get(at), 0, byLaw.get(at).size()).indent(4).strip())
                    .append(" }\n");
        }
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(module.toString()),
                getClass().getClassLoader());
        List<String> broken = new ArrayList<>();
        List<String> neverAnswered = new ArrayList<>();
        for (int at = 0; at < byLaw.size(); at++) {
            Object behavior = Emitted.behavior(loader, "demo", "law" + at)
                    .getConstructor().newInstance();
            List<Check> checks = byLaw.get(at);
            int answered = 0;
            for (int k = 0; k < checks.size(); k++) {
                Object in = Codecs.decoded(loader, "demo.In", Map.of("k", (long) k));
                Object out;
                try {
                    out = Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in));
                } catch (RuntimeException stopped) {
                    if (!stopsOnItsArguments(stopped)) {
                        throw stopped;
                    }
                    continue;
                }
                answered++;
                if (!Boolean.TRUE.equals(((Map<?, ?>) out).get("holds"))) {
                    Check check = checks.get(k);
                    broken.add(check.operation() + " " + check.observed() + " over "
                            + check.arguments());
                }
            }
            if (answered == 0) {
                neverAnswered.add(checks.getFirst().operation() + " "
                        + checks.getFirst().observed());
            }
        }
        assertEquals(List.of(), broken);
        assertEquals(List.of(), neverAnswered, "a law held to no call that answered");
    }

    /** Whether {@code stopped} is the operation refusing its arguments, which a law is silent on. */
    private static boolean stopsOnItsArguments(Throwable stopped) {
        for (Throwable cause = stopped; cause != null; cause = cause.getCause()) {
            if (cause.getClass().getSimpleName().equals("ConstraintViolation")) {
                return true;
            }
        }
        return false;
    }

    /** The checks in {@code [from, to)}, chosen by the input's {@code k} without evaluating any
     *  other: a call that stops on its arguments stops only the run that asked for it. */
    private static String chosen(List<Check> checks, int from, int to) {
        if (to - from == 1) {
            return checks.get(from).holds();
        }
        int middle = (from + to) / 2;
        return "if i.k < " + middle + " then (\n" + chosen(checks, from, middle).indent(4)
                + ") else (\n" + chosen(checks, middle, to).indent(4) + ")";
    }

    /** One check of {@code law} for each choice of values for {@code operation}'s arguments. */
    private static List<Check> checksOf(ValueName.Stdlib.Operation operation,
                                        OperationLaw<DeclaredArgument> law) {
        Stdlib.Signature declaration = DefaultStdlib.get().entry(operation).signature();
        List<Type> params = declaration.params().stream().map(
                EveryLawHoldsOfWhatTheLibraryComputesTest::instantiated).toList();
        Type answers = instantiated(declaration.result());
        List<List<String>> choices = List.of(List.of());
        for (Type param : params) {
            List<List<String>> longer = new ArrayList<>();
            for (List<String> chosen : choices) {
                for (String value : valuesOf(param)) {
                    List<String> next = new ArrayList<>(chosen);
                    next.add(value);
                    longer.add(next);
                }
            }
            choices = longer;
        }
        List<Check> out = new ArrayList<>();
        for (List<String> chosen : choices) {
            // A closure is written where it is handed, where what it is handed says what its
            // parameters are, and where the law applies it, as its body over what it is handed.
            Writer writer = new Writer(params, chosen);
            StringBuilder block = new StringBuilder("{\n");
            List<String> handed = new ArrayList<>();
            for (int i = 0; i < chosen.size(); i++) {
                if (params.get(i) instanceof Type.FnOf) {
                    handed.add(chosen.get(i));
                } else {
                    block.append("    let a").append(i).append(" = ").append(chosen.get(i))
                            .append('\n');
                    handed.add("a" + i);
                }
            }
            // A value the library names, such as an empty set, is written on its own.
            String call = params.isEmpty() ? operation.qualified()
                    : operation.qualified() + "(" + String.join(", ", handed) + ")";
            String held = switch (law) {
                case OperationLaw.Observation<DeclaredArgument>(AnswerAspect aspect,
                                                                var equivalentTo) ->
                        "(" + observed(call, answers, aspect) + ") == (" + writer.of(equivalentTo)
                                + ")";
                case OperationLaw.Size<DeclaredArgument>(var equalTo) ->
                        sizeOf(call, answers) + " == (" + writer.number(equalTo) + ")";
            };
            block.append("    ").append(held).append("\n}");
            out.add(new Check(operation.qualified(), law.observed(), chosen, block.toString()));
        }
        return out;
    }

    /** {@code type} with every type variable an {@code Int}. */
    private static Type instantiated(Type type) {
        return switch (type) {
            case Type.Var _ -> Type.INT;
            case Type.ListOf(Type element) -> new Type.ListOf(instantiated(element));
            case Type.SetOf(Type element) -> new Type.SetOf(instantiated(element));
            case Type.OptionOf(Type element) -> new Type.OptionOf(instantiated(element));
            case Type.MapOf(Type key, Type value) ->
                    new Type.MapOf(instantiated(key), instantiated(value));
            case Type.TupleOf(List<Type> elements) -> new Type.TupleOf(
                    elements.stream().map(EveryLawHoldsOfWhatTheLibraryComputesTest::instantiated)
                            .toList());
            case Type.FnOf(List<Type> params, Type result) -> new Type.FnOf(
                    params.stream().map(EveryLawHoldsOfWhatTheLibraryComputesTest::instantiated)
                            .toList(), instantiated(result));
            default -> type;
        };
    }

    /** The values an argument of {@code type} is written as: the edges a law over it turns on. */
    private static List<String> valuesOf(Type type) {
        // An empty list is written as what dropping all of one leaves, so it has an element type.
        List<String> ints = List.of("List.drop(9, [0])", "[0]", "[1, -1]", "[3, 3]");
        List<String> pairs = List.of("List.drop(9, [(0, 0)])", "[(1, 1)]", "[(1, 1), (1, 2)]",
                "[(1, 0), (2, 3)]");
        return switch (type) {
            case Type.Prim prim when prim == Type.Prim.INT -> List.of("-1", "0", "1", "3");
            case Type.Prim prim when prim == Type.Prim.STRING ->
                    List.of("\"\"", "\" \"", "\"a\"", "\"A b\"", "\"İ\"");
            case Type.Prim prim when prim == Type.Prim.BOOL -> List.of("true", "false");
            case Type.Prim prim when prim == Type.Prim.DECIMAL ->
                    List.of("Decimal.fromInt(0)", "Decimal.fromInt(-3)");
            case Type.ListOf(Type.Prim prim) when prim == Type.Prim.INT -> ints;
            case Type.ListOf(Type.Prim prim) when prim == Type.Prim.STRING ->
                    List.of("List.drop(9, [\"\"])", "[\"\"]", "[\"a\"]", "[\"\", \" \"]",
                            "[\"a\", \"\"]");
            case Type.ListOf(Type.ListOf _) -> List.of("List.drop(9, [[0]])",
                    "[List.drop(9, [0])]", "[List.drop(9, [0]), [1]]", "[[1], [2, 3]]");
            case Type.ListOf(Type.TupleOf _) -> pairs;
            case Type.SetOf _ -> ints.stream().map(list -> "Set.fromList(" + list + ")").toList();
            case Type.MapOf _ -> pairs.stream().map(list -> "Map.fromList(" + list + ")").toList();
            case Type.OptionOf _ ->
                    List.of("List.find(y -> y > 0, [1])", "List.find(y -> y > 0, [0])");
            case Type.FnOf(List<Type> params, Type result) -> {
                String head = params.size() == 1 ? "v" : "(k, v)";
                List<String> bodies = switch (result) {
                    case Type.Prim prim when prim == Type.Prim.BOOL ->
                            List.of("v > 0", "true", "false");
                    case Type.Prim prim when prim == Type.Prim.INT -> List.of("v + 1", "0");
                    case Type.OptionOf _ -> List.of("List.find(y -> y > 0, [v])");
                    case Type.ListOf _ -> List.of("if v > 0 then [v, v] else []");
                    default -> throw new IllegalStateException("no closure answering "
                            + Type.show(result) + " is written here");
                };
                yield bodies.stream().map(body -> head + " -> " + body).toList();
            }
            default -> throw new IllegalStateException("no value of " + Type.show(type)
                    + " is written here");
        };
    }

    /** {@code value}, of {@code type}, coming out on {@code aspect}'s holding side. */
    private static String observed(String value, Type type, AnswerAspect aspect) {
        return switch (aspect) {
            case TRUTH -> value;
            case EMPTINESS -> "Bool.not(" + moduleOf(type) + ".isEmpty(" + value + "))";
            case PRESENCE -> "Option.withDefault(false, Option.map(y -> true, " + value + "))";
        };
    }

    private static String sizeOf(String value, Type type) {
        return switch (moduleOf(type)) {
            case "List", "String" -> moduleOf(type) + ".length(" + value + ")";
            default -> moduleOf(type) + ".size(" + value + ")";
        };
    }

    private static String moduleOf(Type type) {
        return switch (type) {
            case Type.ListOf _ -> "List";
            case Type.SetOf _ -> "Set";
            case Type.MapOf _ -> "Map";
            case Type.Prim prim when prim == Type.Prim.STRING -> "String";
            default -> throw new IllegalStateException(Type.show(type) + " holds nothing");
        };
    }

    /** A law written as Souther over the arguments {@code a0}, {@code a1}, … */
    private static final class Writer {

        private final List<Type> params;
        private final List<String> chosen;
        /** The containers some element of which is being written of, by argument. */
        private final Map<Integer, Integer> within = new LinkedHashMap<>();

        Writer(List<Type> params, List<String> chosen) {
            this.params = params;
            this.chosen = chosen;
        }

        String of(LawProposition<DeclaredArgument> law) {
            return switch (law) {
                case LawProposition.Always<DeclaredArgument>(boolean holds) -> String.valueOf(holds);
                case LawProposition.All<DeclaredArgument> all -> joined(all.parts(), " && ");
                case LawProposition.Any<DeclaredArgument> any -> joined(any.parts(), " || ");
                case LawProposition.Observed<DeclaredArgument> observed -> {
                    String side = observed(subject(observed.of()), typeOf(observed.of()),
                            observed.side().aspect());
                    yield observed.side().holds() ? side : "Bool.not(" + side + ")";
                }
                case LawProposition.Compared<DeclaredArgument> compared ->
                        "(" + number(compared.form()) + ") " + spelled(compared.states()) + " 0";
                case LawProposition.SomeElement<DeclaredArgument> some -> {
                    String any = "List.any(" + element(some.container().position(),
                            of(some.ofTheElement(), some.container())) + ", "
                            + listed(some.container()) + ")";
                    yield some.holds() ? any : "Bool.not(" + any + ")";
                }
                case LawProposition.Same<DeclaredArgument> same -> "(" + subject(same.one())
                        + (same.holds() ? " == " : " /= ") + subject(same.other()) + ")";
            };
        }

        private String of(LawProposition<DeclaredArgument> law, DeclaredArgument container) {
            within.put(container.position(), container.position());
            try {
                return of(law);
            } finally {
                within.remove(container.position());
            }
        }

        private String joined(List<LawProposition<DeclaredArgument>> parts, String by) {
            return "(" + String.join(by, parts.stream().map(this::of).toList()) + ")";
        }

        String number(LinearForm<LawNumber<DeclaredArgument>> form) {
            StringBuilder out = new StringBuilder("(" + whole(form.constant()) + ")");
            form.coefs().forEach((number, by) -> out.append(" + (").append(whole(by)).append(") * ")
                    .append(switch (number) {
                        case LawNumber.AnArgument<DeclaredArgument>(DeclaredArgument at) ->
                                "a" + at.position();
                        case LawNumber.SizeOf<DeclaredArgument>(var of) ->
                                sizeOf(subject(of), typeOf(of));
                        case LawNumber.HowManyMeet<DeclaredArgument> counted ->
                                "List.length(List.filter(" + element(counted.container().position(),
                                        of(counted.ofTheElement(), counted.container())) + ", "
                                        + listed(counted.container()) + "))";
                    }));
            return out.toString();
        }

        /** A closure over an element of the container at {@code position}, as its list holds it. */
        private String element(int position, String body) {
            return params.get(position) instanceof Type.MapOf
                    ? "kv" + position + " -> {\n    let (k" + position + ", e" + position + ") = kv"
                            + position + "\n    " + body + "\n}"
                    : "e" + position + " -> " + body;
        }

        /** The container at {@code container}, as a list of what it holds. */
        private String listed(DeclaredArgument container) {
            return switch (params.get(container.position())) {
                case Type.ListOf _ -> "a" + container.position();
                case Type.SetOf _ -> "Set.toList(a" + container.position() + ")";
                case Type.MapOf _ -> "Map.toList(a" + container.position() + ")";
                default -> throw new IllegalStateException("no element of a "
                        + Type.show(params.get(container.position())));
            };
        }

        private String subject(LawSubject<DeclaredArgument> subject) {
            return switch (subject) {
                case LawSubject.Argument<DeclaredArgument>(DeclaredArgument at) ->
                        "a" + at.position();
                case LawSubject.ElementOf<DeclaredArgument>(DeclaredArgument at) ->
                        "e" + at.position();
                case LawSubject.WhatTheClosureAnswers<DeclaredArgument>(DeclaredArgument at) -> {
                    int container = within.keySet().stream().reduce((a, b) -> b).orElseThrow();
                    String closure = chosen.get(at.position());
                    String body = closure.substring(closure.indexOf("->") + 2).strip();
                    yield "(" + body.replaceAll("\\bv\\b", "e" + container)
                            .replaceAll("\\bk\\b", "k" + container) + ")";
                }
            };
        }

        private Type typeOf(LawSubject<DeclaredArgument> subject) {
            return switch (subject) {
                case LawSubject.Argument<DeclaredArgument>(DeclaredArgument at) ->
                        params.get(at.position());
                case LawSubject.ElementOf<DeclaredArgument>(DeclaredArgument at) ->
                        switch (params.get(at.position())) {
                            case Type.ListOf(Type element) -> element;
                            case Type.SetOf(Type element) -> element;
                            case Type.MapOf(Type _, Type value) -> value;
                            default -> throw new IllegalStateException("no element");
                        };
                case LawSubject.WhatTheClosureAnswers<DeclaredArgument>(DeclaredArgument at) ->
                        ((Type.FnOf) params.get(at.position())).result();
            };
        }

        private static String whole(ExactRatio ratio) {
            if (!ratio.isWhole()
                    || !(ratio.floor() instanceof ExactAnswer.Held<BigInteger>(BigInteger whole))) {
                throw new IllegalStateException("a law over whole numbers is written in them");
            }
            return whole.toString();
        }

        private static String spelled(Rel rel) {
            return switch (rel) {
                case GE -> ">=";
                case GT -> ">";
                case LE -> "<=";
                case LT -> "<";
                case EQ -> "==";
                case NE -> "/=";
            };
        }
    }
}
