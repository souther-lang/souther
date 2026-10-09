package souther.compiler;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;

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
import souther.runtime.ConstraintViolation;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

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
 *
 * <p>The values arrive as the input of a behavior written once per law, and the closures, which no
 * input carries, are chosen by a number the input carries beside them. So what is compiled grows
 * with the laws and the closures and not with the values each is run over.
 */
class EveryLawHoldsOfWhatTheLibraryComputesTest {

    /** A value an argument is given: as the input carries it, and as a report shows it. */
    private record Value(Object raw, String shown) {}

    /** One check of one law: what its arguments are, and the input that hands them over. */
    private record Check(String operation, OperationLaw.Observed observed, List<String> arguments,
                         Map<String, Object> input) {}

    /** A law written as a behavior over its arguments, and the checks that run it. */
    private record Law(String written, List<Check> checks) {}

    /** Each observation's laws on their own, so what one case compiles is that observation's. */
    @ParameterizedTest
    @EnumSource(OperationLaw.Observed.class)
    void everyLawHoldsWhereItsOperationAnswers(OperationLaw.Observed of) throws Exception {
        List<Law> byLaw = new ArrayList<>();
        DefaultBoundOperationFacts.get().settled().forEach((operation, settled) ->
                settled.forEach((observed, settling) -> {
                    if (observed == of && settling instanceof BoundOperationFacts.Settled.ByALaw(
                            var law, var _)) {
                        byLaw.add(lawOf(byLaw.size(), (ValueName.Stdlib.Operation) operation,
                                law));
                    }
                }));
        StringBuilder module = new StringBuilder("module demo\n\ndata Out = { holds: Bool }\n");
        byLaw.forEach(law -> module.append('\n').append(law.written()));
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(module.toString()),
                getClass().getClassLoader());
        List<String> broken = new ArrayList<>();
        List<String> neverAnswered = new ArrayList<>();
        for (int at = 0; at < byLaw.size(); at++) {
            Object behavior = Emitted.behavior(loader, "demo", "law" + at)
                    .getConstructor().newInstance();
            int answered = 0;
            for (Check check : byLaw.get(at).checks()) {
                Object in = Codecs.decoded(loader, "demo.In" + at, check.input());
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
                    broken.add(check.operation() + " " + check.observed() + " over "
                            + check.arguments());
                }
            }
            if (answered == 0) {
                Check first = byLaw.get(at).checks().getFirst();
                neverAnswered.add(first.operation() + " " + first.observed());
            }
        }
        assertEquals(List.of(), broken);
        assertEquals(List.of(), neverAnswered, "a law held to no call that answered");
    }

    /** Whether {@code stopped} is the operation refusing its arguments, which a law is silent on. */
    private static boolean stopsOnItsArguments(Throwable stopped) {
        for (Throwable cause = stopped; cause != null; cause = cause.getCause()) {
            if (cause instanceof ConstraintViolation) {
                return true;
            }
        }
        return false;
    }

    /**
     * {@code law} of {@code operation} written as the behavior {@code law<index>} over the input
     * {@code In<index>}, and one check for each choice of values for its arguments.
     */
    private static Law lawOf(int index, ValueName.Stdlib.Operation operation,
                             OperationLaw<DeclaredArgument> law) {
        Stdlib.Signature declaration = DefaultStdlib.get().entry(operation).signature();
        Set<Type> keys = new HashSet<>();
        declaration.params().forEach(each -> keysIn(each, keys));
        keysIn(declaration.result(), keys);
        List<Type> params = declaration.params().stream()
                .map(each -> instantiated(each, keys)).toList();
        Type answers = instantiated(declaration.result(), keys);
        // Each closure the law is run with is written into the behavior, chosen by the input's
        // `c`; every other argument is a field of the input.
        List<List<String>> closures = List.of(new ArrayList<>(params.size()));
        List<List<Value>> values = List.of(List.of());
        for (Type param : params) {
            List<List<String>> moreClosures = new ArrayList<>();
            for (List<String> chosen : closures) {
                for (String closure : param instanceof Type.FnOf ? closuresOf(param)
                        : Collections.<String>singletonList(null)) {
                    List<String> next = new ArrayList<>(chosen);
                    next.add(closure);
                    moreClosures.add(next);
                }
            }
            closures = moreClosures;
            if (!(param instanceof Type.FnOf)) {
                List<List<Value>> moreValues = new ArrayList<>();
                for (List<Value> chosen : values) {
                    for (Value value : valuesOf(param)) {
                        List<Value> next = new ArrayList<>(chosen);
                        next.add(value);
                        moreValues.add(next);
                    }
                }
                values = moreValues;
            }
        }
        StringBuilder written = new StringBuilder("data In" + index + " = { c: Int");
        for (int i = 0; i < params.size(); i++) {
            switch (params.get(i)) {
                case Type.FnOf _ -> { }
                // A pair crosses no boundary, so a list of them arrives as its two halves.
                case Type.ListOf(Type.TupleOf(List<Type> pair)) ->
                        written.append(", a").append(i).append("k: List<")
                                .append(Type.show(pair.get(0))).append(">, a").append(i)
                                .append("v: List<").append(Type.show(pair.get(1))).append('>');
                default -> written.append(", a").append(i).append(": ")
                        .append(Type.show(params.get(i)));
            }
        }
        written.append(" }\n\nbehavior law").append(index).append(" : (i: In").append(index)
                .append(") -> Out constructs Out\nlet law").append(index)
                .append(" (i) = Out { holds = ");
        List<String> blocks = new ArrayList<>();
        for (List<String> chosen : closures) {
            StringBuilder block = new StringBuilder("{\n");
            List<String> handed = new ArrayList<>();
            for (int i = 0; i < params.size(); i++) {
                if (chosen.get(i) != null) {
                    handed.add(chosen.get(i));
                } else {
                    block.append("    let a").append(i).append(" = ")
                            .append(params.get(i) instanceof Type.ListOf(Type.TupleOf _)
                                    ? "List.zipShortest(i.a" + i + "k, i.a" + i + "v)"
                                    : "i.a" + i).append('\n');
                    handed.add("a" + i);
                }
            }
            block.append("    ").append(held(operation, law, answers, handed,
                    new Writer(params, chosen))).append("\n}");
            blocks.add(block.toString());
        }
        written.append(chosen(blocks, 0, blocks.size()).indent(4).strip()).append(" }\n");
        List<Check> checks = new ArrayList<>();
        for (int c = 0; c < closures.size(); c++) {
            for (List<Value> chosen : values) {
                Map<String, Object> input = new HashMap<>();
                input.put("c", (long) c);
                List<String> shown = new ArrayList<>();
                int field = 0;
                for (int i = 0; i < params.size(); i++) {
                    if (closures.get(c).get(i) != null) {
                        shown.add(closures.get(c).get(i));
                    } else {
                        Value value = chosen.get(field++);
                        if (params.get(i) instanceof Type.ListOf(Type.TupleOf _)) {
                            List<Object> firsts = new ArrayList<>();
                            List<Object> held = new ArrayList<>();
                            for (Object pair : (List<?>) value.raw()) {
                                firsts.add(((List<?>) pair).get(0));
                                held.add(((List<?>) pair).get(1));
                            }
                            input.put("a" + i + "k", firsts);
                            input.put("a" + i + "v", held);
                        } else {
                            input.put("a" + i, value.raw());
                        }
                        shown.add(value.shown());
                    }
                }
                checks.add(new Check(operation.qualified(), law.observed(), shown, input));
            }
        }
        return new Law(written.toString(), checks);
    }

    /** The blocks in {@code [from, to)}, chosen by the input's {@code c} without evaluating any
     *  other. */
    private static String chosen(List<String> blocks, int from, int to) {
        if (to - from == 1) {
            return blocks.get(from);
        }
        int middle = (from + to) / 2;
        return "if i.c < " + middle + " then (\n" + chosen(blocks, from, middle).indent(4)
                + ") else (\n" + chosen(blocks, middle, to).indent(4) + ")";
    }

    /** That {@code operation} handed {@code handed} answers as {@code law} says, written by
     *  {@code writer}. */
    private static String held(ValueName.Stdlib.Operation operation,
                               OperationLaw<DeclaredArgument> law, Type answers,
                               List<String> handed, Writer writer) {
        // A value the library names, such as an empty set, is written on its own.
        String call = handed.isEmpty() ? operation.qualified()
                : operation.qualified() + "(" + String.join(", ", handed) + ")";
        return switch (law) {
            case OperationLaw.Observation<DeclaredArgument>(AnswerAspect aspect,
                                                            var equivalentTo) ->
                    "(" + observed(call, answers, aspect) + ") == (" + writer.of(equivalentTo) + ")";
            case OperationLaw.Size<DeclaredArgument>(var equalTo) ->
                    sizeOf(call, answers) + " == (" + writer.number(equalTo) + ")";
        };
    }

    /** {@code type} with every variable a map is keyed by, in {@code keys}, a {@code String} —
     *  which is what a map that crosses is keyed by — and every other type variable an
     *  {@code Int}. */
    private static Type instantiated(Type type, Set<Type> keys) {
        return switch (type) {
            case Type.Var _ -> keys.contains(type) ? Type.STRING : Type.INT;
            case Type.ListOf(Type element) -> new Type.ListOf(instantiated(element, keys));
            case Type.SetOf(Type element) -> new Type.SetOf(instantiated(element, keys));
            case Type.OptionOf(Type element) -> new Type.OptionOf(instantiated(element, keys));
            case Type.MapOf(Type key, Type value) ->
                    new Type.MapOf(instantiated(key, keys), instantiated(value, keys));
            case Type.TupleOf(List<Type> elements) -> new Type.TupleOf(
                    elements.stream().map(each -> instantiated(each, keys)).toList());
            case Type.FnOf(List<Type> params, Type result) -> new Type.FnOf(
                    params.stream().map(each -> instantiated(each, keys)).toList(),
                    instantiated(result, keys));
            default -> type;
        };
    }

    /** The type variables {@code type} keys a map by, added to {@code into}. */
    private static void keysIn(Type type, Set<Type> into) {
        switch (type) {
            case Type.MapOf(Type key, Type value) -> {
                if (key instanceof Type.Var) {
                    into.add(key);
                }
                keysIn(value, into);
            }
            case Type.ListOf(Type element) -> keysIn(element, into);
            case Type.SetOf(Type element) -> keysIn(element, into);
            case Type.OptionOf(Type element) -> keysIn(element, into);
            case Type.TupleOf(List<Type> elements) -> elements.forEach(each -> keysIn(each, into));
            case Type.FnOf(List<Type> params, Type result) -> {
                params.forEach(each -> keysIn(each, into));
                keysIn(result, into);
            }
            default -> { }
        }
    }

    /** The values an argument of {@code type} is given: the edges a law over it turns on. */
    private static List<Value> valuesOf(Type type) {
        List<List<Long>> ints = List.of(List.of(), List.of(0L), List.of(1L, -1L), List.of(3L, 3L));
        return switch (type) {
            case Type.Prim prim when prim == Type.Prim.INT ->
                    List.of(-1L, 0L, 1L, 3L).stream().map(n -> new Value(n, n.toString())).toList();
            case Type.Prim prim when prim == Type.Prim.STRING ->
                    List.of("", " ", "a", "A b", "İ").stream()
                            .map(s -> new Value(s, '"' + s + '"')).toList();
            case Type.Prim prim when prim == Type.Prim.BOOL ->
                    List.of(new Value(true, "true"), new Value(false, "false"));
            case Type.Prim prim when prim == Type.Prim.DECIMAL ->
                    List.of(new Value(new BigDecimal("0"), "0"),
                            new Value(new BigDecimal("-3.5"), "-3.5"));
            case Type.ListOf(Type.Prim prim) when prim == Type.Prim.INT ->
                    ints.stream().map(list -> new Value(list, list.toString())).toList();
            case Type.ListOf(Type.Prim prim) when prim == Type.Prim.STRING ->
                    List.of(List.of(), List.of(""), List.of("a"), List.of("", " "),
                                    List.of("a", "")).stream()
                            .map(list -> new Value(list, list.toString())).toList();
            case Type.ListOf(Type.ListOf _) -> List.of(List.<List<Long>>of(), List.of(List.of()),
                            List.of(List.of(), List.of(1L)), List.of(List.of(1L), List.of(2L, 3L)))
                    .stream().map(list -> new Value(list, list.toString())).toList();
            // Entries of a map keyed by strings, one key given twice.
            case Type.ListOf(Type.TupleOf _) -> List.of(List.<List<Object>>of(),
                            List.of(List.<Object>of("a", 1L)),
                            List.of(List.<Object>of("a", 1L), List.<Object>of("a", 2L)),
                            List.of(List.<Object>of("a", 0L), List.<Object>of("b", 3L)))
                    .stream().map(list -> new Value(list, list.toString())).toList();
            case Type.SetOf _ -> List.of(List.<Long>of(), List.of(0L), List.of(1L, -1L))
                    .stream().map(set -> new Value(set, "set " + set)).toList();
            case Type.MapOf _ -> List.of(Map.<String, Long>of(), Map.of("a", 1L),
                            Map.of("a", 0L, "b", 3L))
                    .stream().map(map -> new Value(map, "map " + map)).toList();
            case Type.OptionOf _ -> List.of(new Value(null, "none"), new Value(1L, "some 1"));
            default -> throw new IllegalStateException("no value of " + Type.show(type)
                    + " is written here");
        };
    }

    /** The closures an argument of {@code type} is handed as: true of every element, of none, of
     *  some, and what each other kind of answer has at its edges. */
    private static List<String> closuresOf(Type type) {
        Type.FnOf fn = (Type.FnOf) type;
        String head = fn.params().size() == 1 ? "v" : "(k, v)";
        List<String> bodies = switch (fn.result()) {
            case Type.Prim prim when prim == Type.Prim.BOOL -> List.of("v > 0", "true", "false");
            case Type.Prim prim when prim == Type.Prim.INT -> List.of("v + 1", "0");
            // A key: one per value, or one for all of them.
            case Type.Prim prim when prim == Type.Prim.STRING ->
                    List.of("String.fromInt(v)", "\"same\"");
            case Type.OptionOf _ -> List.of("List.find(y -> y > 0, [v])");
            case Type.ListOf _ -> List.of("if v > 0 then [v, v] else []");
            default -> throw new IllegalStateException("no closure answering "
                    + Type.show(fn.result()) + " is written here");
        };
        return bodies.stream().map(body -> head + " -> " + body).toList();
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
        /** The closure handed at each argument, or null where the argument is no closure. */
        private final List<String> closures;
        /** The containers some element of which is being written of, by argument. */
        private final Map<Integer, Integer> within = new LinkedHashMap<>();

        Writer(List<Type> params, List<String> closures) {
            this.params = params;
            this.closures = closures;
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
                // The closure's body over what it is handed, which is the element where it stands.
                case LawSubject.WhatTheClosureAnswers<DeclaredArgument>(DeclaredArgument at) -> {
                    int container = within.keySet().stream().reduce((a, b) -> b).orElseThrow();
                    String closure = closures.get(at.position());
                    String body = closure.substring(closure.indexOf("->") + 2).strip();
                    yield "(" + body.replaceAll("\\bv\\b", "e" + container)
                            .replaceAll("\\bk\\b", "k" + container) + ")";
                }
                case LawSubject.KeyOf<DeclaredArgument>(DeclaredArgument at) -> "k" + at.position();
                case LawSubject.AnswerOf<DeclaredArgument> _ -> throw new IllegalStateException(
                        "a law names what another operation answers: " + subject);
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
                case LawSubject.KeyOf<DeclaredArgument>(DeclaredArgument at) ->
                        Type.keyOf(params.get(at.position()));
                case LawSubject.AnswerOf<DeclaredArgument> _ -> throw new IllegalStateException(
                        "a law names what another operation answers: " + subject);
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
