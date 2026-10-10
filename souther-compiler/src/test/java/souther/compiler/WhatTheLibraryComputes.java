package souther.compiler;

import souther.compiler.check.DeclaredArgument;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.proof.ByPlace;
import souther.compiler.proof.Slot;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.semantics.SideAnswered;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;
import souther.runtime.ConstraintViolation;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.function.Supplier;

/**
 * Statements about what the library's operations answer, written as Souther over the values each
 * is about and run over values chosen at the edges a statement turns on.
 *
 * <p>What is run is written from the statement itself — the operation's answer, its arguments by
 * place, and any value at all, each a value a behavior is handed or computes — so no statement is
 * run in words of its own. A run over finitely many values is evidence and not a proof: the values
 * are the edges a statement turns on — a count below nought, at nought, at and past the end; a
 * container empty, holding one, holding a value twice; a closure true of every element, of none, of
 * some; a string empty, blank, widening under a case mapping, and changing where it is put beside
 * another. A statement says nothing of a call that stops on its arguments, so a call that stops is
 * not held to it, and every statement is still held to one that does not.
 *
 * <p>The values arrive as the input of a behavior written once per statement, and the closures,
 * which no input carries, are chosen by a number the input carries beside them. So what is compiled
 * grows with the statements and the closures and not with the values each is run over.
 */
public final class WhatTheLibraryComputes {

    private WhatTheLibraryComputes() {}

    /**
     * A statement about what {@code operation} answers: over its arguments by place
     * ({@link Slot.Place}), any value ({@link Slot.Every}), and its answer handed its own arguments
     * ({@link Slot.Answer}). {@code what} names it in a report.
     */
    public record Statement(ValueName.Stdlib.Operation operation, String what,
                            LawProposition<Slot> holds) {}

    /** The statements found false of a call that answered, and the ones held to no call that
     *  answered. */
    public record Held(List<String> broken, List<String> neverAnswered) {}

    /** {@code law} of {@code operation}, as the statement that its answer comes out as the law
     *  says. */
    public static Statement ofALaw(ValueName.Stdlib.Operation operation,
                                   OperationLaw<DeclaredArgument> law) {
        LawSubject<Slot> answer = new LawSubject.Argument<>(new Slot.Answer());
        LawProposition<Slot> holds = switch (ByPlace.<DeclaredArgument, Slot>law(law,
                at -> new Slot.Place(at.position()))) {
            case OperationLaw.Observation<Slot>(AnswerAspect aspect,
                                                LawProposition<Slot> equivalentTo) -> {
                LawProposition<Slot> side = new LawProposition.Observed<>(answer,
                        new SideAnswered(aspect, true));
                yield new LawProposition.Any<>(List.of(
                        new LawProposition.All<>(List.of(side, equivalentTo)),
                        new LawProposition.All<>(List.of(side.denied(), equivalentTo.denied()))));
            }
            // One of the cases met, and as many as it says there.
            case OperationLaw.Size<Slot>(var cases) -> {
                List<LawProposition<Slot>> each = cases.stream()
                        .<LawProposition<Slot>>map(one -> new LawProposition.All<>(List.of(
                                one.where(), new LawProposition.Compared<>(
                                        differenceOf(answer, one.equalTo()), Rel.EQ))))
                        .toList();
                yield each.size() == 1 ? each.getFirst() : new LawProposition.Any<>(each);
            }
        };
        return new Statement(operation, law.observed().toString(), holds);
    }

    /** How many {@code of} holds less what {@code form} comes to. */
    private static LinearForm<LawNumber<Slot>> differenceOf(LawSubject<Slot> of,
                                                            LinearForm<LawNumber<Slot>> form) {
        Map<LawNumber<Slot>, ExactRatio> coefs = new LinkedHashMap<>();
        form.coefs().forEach((number, by) -> coefs.put(number, by.negated()));
        if (coefs.put(new LawNumber.SizeOf<>(of), ExactRatio.ONE) != null) {
            throw new IllegalStateException("a law's number names its own answer: " + form);
        }
        return new LinearForm<>(form.constant().negated(), coefs);
    }

    /** Every statement in {@code statements}, run. */
    public static Held run(List<Statement> statements) throws Exception {
        List<Written> written = new ArrayList<>();
        for (Statement statement : statements) {
            written.add(written(written.size(), statement));
        }
        StringBuilder module = new StringBuilder("module demo\n\ndata Out = { holds: Bool }\n");
        written.forEach(each -> module.append('\n').append(each.source()));
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(module.toString()),
                WhatTheLibraryComputes.class.getClassLoader());
        List<String> broken = new ArrayList<>();
        List<String> neverAnswered = new ArrayList<>();
        for (int at = 0; at < written.size(); at++) {
            Object behavior = Emitted.behavior(loader, "demo", "statement" + at)
                    .getConstructor().newInstance();
            Statement statement = statements.get(at);
            int answered = 0;
            for (Check check : written.get(at).checks()) {
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
                    broken.add(statement.operation().qualified() + " " + statement.what()
                            + " over " + check.arguments());
                }
            }
            if (answered == 0) {
                neverAnswered.add(statement.operation().qualified() + " " + statement.what());
            }
        }
        return new Held(broken, neverAnswered);
    }

    /** Whether {@code stopped} is the operation refusing its arguments, which a statement is
     *  silent on. */
    public static boolean stopsOnItsArguments(Throwable stopped) {
        for (Throwable cause = stopped; cause != null; cause = cause.getCause()) {
            if (cause instanceof ConstraintViolation) {
                return true;
            }
        }
        return false;
    }

    /** A program compiled once, whose behaviors are run over inputs handed as plain values. */
    public static final class Program {

        private final BytesClassLoader loader;
        private final String module;

        public Program(String module, String source) {
            this.module = module;
            this.loader = new BytesClassLoader(Compiler.compile(source),
                    WhatTheLibraryComputes.class.getClassLoader());
        }

        /** What {@code behavior}, handed {@code input} as the record {@code in}, answers, as the
         *  record {@code out} is written out. */
        public Object answer(String behavior, String in, String out, Map<String, Object> input)
                throws Exception {
            Object running = Emitted.behavior(loader, module, behavior).getConstructor()
                    .newInstance();
            Object handed = Codecs.decoded(loader, module + "." + in, input);
            return Codecs.encode(loader, module + "." + out, Codecs.apply(running, handed));
        }
    }

    /** A value an argument is given: as the input carries it, and as a report shows it. */
    private record Value(Object raw, String shown) {}

    /** One run of one statement: what its values are, and the input that hands them over. */
    private record Check(List<String> arguments, Map<String, Object> input) {}

    /** A statement written as a behavior, and the runs of it. */
    private record Written(String source, List<Check> checks) {}

    /** {@code statement} written as the behavior {@code statement<index>} over the input
     *  {@code In<index>}, and one check for each choice of values for what it is about. */
    private static Written written(int index, Statement statement) {
        ValueName.Stdlib.Operation operation = statement.operation();
        Stdlib.Signature declaration = DefaultStdlib.get().entry(operation).signature();
        List<Type> params = instantiated(declaration.params(), declaration);
        Type answers = instantiated(List.of(declaration.result()), declaration).getFirst();
        Map<Integer, Type> every = everyIn(statement.holds(), params, answers);
        // Each closure the statement is run with is written into the behavior, chosen by the
        // input's `c`; every other argument, and every value it is about, is a field of the input.
        List<List<String>> closures = List.of(new ArrayList<>(params.size()));
        for (Type param : params) {
            List<List<String>> more = new ArrayList<>();
            for (List<String> chosen : closures) {
                for (String closure : param instanceof Type.FnOf ? closuresOf(param)
                        : Collections.<String>singletonList(null)) {
                    List<String> next = new ArrayList<>(chosen);
                    next.add(closure);
                    more.add(next);
                }
            }
            closures = more;
        }
        List<String> fields = new ArrayList<>();
        List<Type> carried = new ArrayList<>();
        for (int i = 0; i < params.size(); i++) {
            if (!(params.get(i) instanceof Type.FnOf)) {
                fields.add("a" + i);
                carried.add(params.get(i));
            }
        }
        every.forEach((which, type) -> {
            fields.add("x" + which);
            carried.add(type);
        });
        List<List<Value>> values = List.of(List.of());
        for (Type type : carried) {
            List<List<Value>> more = new ArrayList<>();
            for (List<Value> chosen : values) {
                for (Value value : valuesOf(type)) {
                    List<Value> next = new ArrayList<>(chosen);
                    next.add(value);
                    more.add(next);
                }
            }
            values = more;
        }
        StringBuilder source = new StringBuilder("data In" + index + " = { c: Int");
        for (int at = 0; at < fields.size(); at++) {
            String field = fields.get(at);
            switch (carried.get(at)) {
                // A pair crosses no boundary, so a list of them arrives as its two halves.
                case Type.ListOf(Type.TupleOf(List<Type> pair)) ->
                        source.append(", ").append(field).append("k: List<")
                                .append(Type.show(pair.get(0))).append(">, ").append(field)
                                .append("v: List<").append(Type.show(pair.get(1))).append('>');
                default -> source.append(", ").append(field).append(": ")
                        .append(Type.show(carried.get(at)));
            }
        }
        source.append(" }\n\nbehavior statement").append(index).append(" : (i: In").append(index)
                .append(") -> Out constructs Out\nlet statement").append(index)
                .append(" (i) = Out { holds = ");
        List<String> blocks = new ArrayList<>();
        for (List<String> chosen : closures) {
            StringBuilder block = new StringBuilder("{\n");
            List<String> handed = new ArrayList<>();
            for (int i = 0; i < params.size(); i++) {
                if (chosen.get(i) != null) {
                    handed.add(chosen.get(i));
                } else {
                    handed.add("a" + i);
                }
            }
            for (int at = 0; at < fields.size(); at++) {
                String field = fields.get(at);
                block.append("    let ").append(field).append(" = ")
                        .append(carried.get(at) instanceof Type.ListOf(Type.TupleOf _)
                                ? "List.zipShortest(i." + field + "k, i." + field + "v)"
                                : "i." + field).append('\n');
            }
            // A value the library names, such as an empty set, is written on its own.
            String call = handed.isEmpty() ? operation.qualified()
                    : operation.qualified() + "(" + String.join(", ", handed) + ")";
            block.append("    ").append(new Writer(params, chosen, every, call, answers)
                    .of(statement.holds())).append("\n}");
            blocks.add(block.toString());
        }
        source.append(chosen(blocks, 0, blocks.size()).indent(4).strip()).append(" }\n");
        List<Check> checks = new ArrayList<>();
        for (int c = 0; c < closures.size(); c++) {
            for (List<Value> chosen : values) {
                Map<String, Object> input = new HashMap<>();
                input.put("c", (long) c);
                List<String> shown = new ArrayList<>();
                for (int i = 0; i < params.size(); i++) {
                    if (closures.get(c).get(i) != null) {
                        shown.add(closures.get(c).get(i));
                    }
                }
                for (int at = 0; at < fields.size(); at++) {
                    Value value = chosen.get(at);
                    String field = fields.get(at);
                    if (carried.get(at) instanceof Type.ListOf(Type.TupleOf _)) {
                        List<Object> firsts = new ArrayList<>();
                        List<Object> held = new ArrayList<>();
                        for (Object pair : (List<?>) value.raw()) {
                            firsts.add(((List<?>) pair).get(0));
                            held.add(((List<?>) pair).get(1));
                        }
                        input.put(field + "k", firsts);
                        input.put(field + "v", held);
                    } else {
                        input.put(field, value.raw());
                    }
                    shown.add(field + "=" + value.shown());
                }
                checks.add(new Check(shown, input));
            }
        }
        return new Written(source.toString(), checks);
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

    /** {@code types}, each with every variable a map in {@code declaration} is keyed by a
     *  {@code String} — which is what a map that crosses is keyed by — and every other type
     *  variable an {@code Int}. */
    public static List<Type> instantiated(List<Type> types, Stdlib.Signature declaration) {
        Set<Type> keys = new HashSet<>();
        declaration.params().forEach(each -> keysIn(each, keys));
        keysIn(declaration.result(), keys);
        return types.stream().map(each -> instantiated(each, keys)).toList();
    }

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

    /**
     * The type of each value {@code holds} is about by {@link Slot.Every}, read off where it
     * stands: handed to an operation, where it is what that operation takes there; beside a value
     * it is said to be, where it is of that value's type; or a container something is filed in
     * under a key, where it is a map keyed as the maps here are.
     */
    private static Map<Integer, Type> everyIn(LawProposition<Slot> holds, List<Type> params,
                                              Type answers) {
        Map<Integer, Type> every = new TreeMap<>();
        Set<Integer> named = new HashSet<>();
        Set<Integer> keyed = new HashSet<>();
        for (int round = 0; round < 4; round++) {
            new Walk(params, answers, every, named, keyed).proposition(holds);
        }
        for (int which : named) {
            if (!every.containsKey(which) && keyed.contains(which)) {
                every.put(which, new Type.MapOf(Type.STRING, Type.INT));
            }
        }
        if (!every.keySet().containsAll(named)) {
            throw new IllegalStateException("no type is read for every value " + holds
                    + " is about");
        }
        return every;
    }

    /** One pass over a statement for the types of the values it is about. */
    private record Walk(List<Type> params, Type answers, Map<Integer, Type> every,
                        Set<Integer> named, Set<Integer> keyed) {

        void proposition(LawProposition<Slot> holds) {
            switch (holds) {
                case LawProposition.Always<Slot> _ -> { }
                case LawProposition.All<Slot>(var parts) -> parts.forEach(this::proposition);
                case LawProposition.Any<Slot>(var parts) -> parts.forEach(this::proposition);
                case LawProposition.Observed<Slot>(var of, var _) -> subject(of);
                case LawProposition.Compared<Slot>(var form, var _) ->
                        form.coefs().keySet().forEach(this::number);
                case LawProposition.SomeElement<Slot>(var container, var ofTheElement, var _) -> {
                    slot(container);
                    proposition(ofTheElement);
                }
                case LawProposition.Same<Slot>(var one, var other, var _) -> {
                    subject(one);
                    subject(other);
                    alike(one, other);
                    alike(other, one);
                }
            }
        }

        private void number(LawNumber<Slot> number) {
            switch (number) {
                case LawNumber.AnArgument<Slot>(Slot at) -> slot(at);
                case LawNumber.SizeOf<Slot>(var of) -> subject(of);
                case LawNumber.HowManyMeet<Slot>(Slot container, var ofTheElement) -> {
                    slot(container);
                    proposition(ofTheElement);
                }
                case LawNumber.HowManyDifferent<Slot>(Slot container, var ofTheElement) -> {
                    slot(container);
                    subject(ofTheElement);
                }
                case LawNumber.SumOver<Slot>(Slot container, var ofTheElement) -> {
                    slot(container);
                    number(ofTheElement);
                }
            }
        }

        private void subject(LawSubject<Slot> subject) {
            switch (subject) {
                case LawSubject.Argument<Slot>(Slot at) -> slot(at);
                case LawSubject.ElementOf<Slot>(Slot at) -> slot(at);
                case LawSubject.WhatTheClosureAnswers<Slot>(Slot at) -> slot(at);
                case LawSubject.KeyOf<Slot>(Slot at) -> {
                    slot(at);
                    if (at instanceof Slot.Every(int which)) {
                        keyed.add(which);
                    }
                }
                case LawSubject.AnswerOf<Slot>(var operation, var args) -> {
                    Stdlib.Signature declaration = DefaultStdlib.get().entry(operation).signature();
                    List<Type> takes = instantiated(declaration.params(), declaration);
                    for (int at = 0; at < args.size(); at++) {
                        subject(args.get(at));
                        if (args.get(at) instanceof LawSubject.Argument<Slot>(
                                Slot.Every(int which))) {
                            every.putIfAbsent(which, takes.get(at));
                        }
                    }
                }
            }
        }

        private void slot(Slot slot) {
            if (slot instanceof Slot.Every(int which)) {
                named.add(which);
            }
        }

        /** {@code one}, where it is a value the statement is about, of {@code other}'s type. */
        private void alike(LawSubject<Slot> one, LawSubject<Slot> other) {
            if (one instanceof LawSubject.Argument<Slot>(Slot.Every(int which))
                    && !every.containsKey(which)) {
                Type type = new Writer(params, List.of(), every, "", answers).typeOf(other);
                if (type != null) {
                    every.put(which, type);
                }
            }
        }
    }

    /** The values an argument of {@code type} is given: the edges a statement over it turns
     *  on. */
    private static List<Value> valuesOf(Type type) {
        List<List<Long>> ints = List.of(List.of(), List.of(0L), List.of(1L, -1L), List.of(3L, 3L));
        return switch (type) {
            case Type.Prim prim when prim == Type.Prim.INT ->
                    List.of(-1L, 0L, 1L, 3L).stream().map(n -> new Value(n, n.toString())).toList();
            // And text whose canonical form changes where it is put beside other text: a mark
            // that joins a letter before it, and one that joins the letter a mark beside it was
            // already on.
            case Type.Prim prim when prim == Type.Prim.STRING ->
                    List.of("", " ", "a", "A b", "İ", "e", "̂́", "L̄", "̣")
                            .stream().map(s -> new Value(s, '"' + s + '"')).toList();
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

    /** A statement written as Souther over the values it is about. */
    private static final class Writer {

        private final List<Type> params;
        /** The closure handed at each argument, or null where the argument is no closure. */
        private final List<String> closures;
        private final Map<Integer, Type> every;
        /** The operation handed its arguments, written out. */
        private final String call;
        private final Type answers;
        /** The containers some element of which is being written of, the innermost last. */
        private final Deque<Slot> within = new ArrayDeque<>();

        Writer(List<Type> params, List<String> closures, Map<Integer, Type> every, String call,
               Type answers) {
            this.params = params;
            this.closures = closures;
            this.every = every;
            this.call = call;
            this.answers = answers;
        }

        String of(LawProposition<Slot> holds) {
            return switch (holds) {
                case LawProposition.Always<Slot>(boolean always) -> String.valueOf(always);
                case LawProposition.All<Slot> all -> joined(all.parts(), " && ");
                case LawProposition.Any<Slot> any -> joined(any.parts(), " || ");
                case LawProposition.Observed<Slot> observed -> {
                    String side = observed(subject(observed.of()), typeOf(observed.of()),
                            observed.side().aspect());
                    yield observed.side().holds() ? side : "Bool.not(" + side + ")";
                }
                case LawProposition.Compared<Slot> compared ->
                        "(" + number(compared.form()) + ") " + spelled(compared.states()) + " 0";
                case LawProposition.SomeElement<Slot> some -> {
                    String any = "List.any(" + element(some.container(),
                            within(some.ofTheElement(), some.container())) + ", "
                            + listed(some.container()) + ")";
                    yield some.holds() ? any : "Bool.not(" + any + ")";
                }
                case LawProposition.Same<Slot> same -> "(" + subject(same.one())
                        + (same.holds() ? " == " : " /= ") + subject(same.other()) + ")";
            };
        }

        private String within(LawProposition<Slot> holds, Slot container) {
            within.addLast(container);
            try {
                return of(holds);
            } finally {
                within.removeLast();
            }
        }

        private String joined(List<LawProposition<Slot>> parts, String by) {
            return "(" + String.join(by, parts.stream().map(this::of).toList()) + ")";
        }

        String number(LinearForm<LawNumber<Slot>> form) {
            StringBuilder out = new StringBuilder("(" + whole(form.constant()) + ")");
            form.coefs().forEach((number, by) -> out.append(" + (").append(whole(by)).append(") * ")
                    .append(switch (number) {
                        case LawNumber.AnArgument<Slot>(Slot at) -> named(at);
                        case LawNumber.SizeOf<Slot>(var of) -> sizeOf(subject(of), typeOf(of));
                        case LawNumber.HowManyMeet<Slot> counted ->
                                "List.length(List.filter(" + element(counted.container(),
                                        within(counted.ofTheElement(), counted.container()))
                                        + ", " + listed(counted.container()) + "))";
                        // As many as a set of them holds.
                        case LawNumber.HowManyDifferent<Slot> different ->
                                "Set.size(Set.fromList(List.map(" + element(different.container(),
                                        inside(different.container(),
                                                () -> subject(different.ofTheElement())))
                                        + ", " + listed(different.container()) + ")))";
                        case LawNumber.SumOver<Slot> sum ->
                                "List.sum(List.map(" + element(sum.container(),
                                        inside(sum.container(), () -> number(
                                                LinearForm.atom(sum.ofTheElement()))))
                                        + ", " + listed(sum.container()) + "))";
                    }));
            return out.toString();
        }

        /** What {@code write} writes of the element of {@code container}. */
        private String inside(Slot container, Supplier<String> write) {
            within.addLast(container);
            try {
                return write.get();
            } finally {
                within.removeLast();
            }
        }

        /** The value {@code slot} names, written out. */
        private String named(Slot slot) {
            return switch (slot) {
                case Slot.Place(int position) -> "a" + position;
                case Slot.Every(int which) -> "x" + which;
                case Slot.Answer _ -> call;
                case Slot.Carried _, Slot.Walked _ -> throw new IllegalStateException(
                        "a statement run over a call names no walk: " + slot);
            };
        }

        /** What the element of the container at {@code slot} is called where it is written of. */
        private static String elementOf(Slot slot) {
            return "e" + word(slot);
        }

        private static String keyOf(Slot slot) {
            return "k" + word(slot);
        }

        private static String word(Slot slot) {
            return switch (slot) {
                case Slot.Place(int position) -> "a" + position;
                case Slot.Every(int which) -> "x" + which;
                case Slot.Answer _ -> "r";
                case Slot.Carried _, Slot.Walked _ -> throw new IllegalStateException(
                        "a statement run over a call names no walk: " + slot);
            };
        }

        Type typeOf(Slot slot) {
            return switch (slot) {
                case Slot.Place(int position) -> params.get(position);
                case Slot.Every(int which) -> every.get(which);
                case Slot.Answer _ -> answers;
                case Slot.Carried _, Slot.Walked _ -> throw new IllegalStateException(
                        "a statement run over a call names no walk: " + slot);
            };
        }

        /** A closure over an element of the container at {@code container}, as its list holds
         *  it. */
        private String element(Slot container, String body) {
            String element = elementOf(container);
            return switch (typeOf(container)) {
                case Type.MapOf _ -> "kv" + element + " -> {\n    let (" + keyOf(container) + ", "
                        + element + ") = kv" + element + "\n    " + body + "\n}";
                // An entry of a list of them is filed under its first.
                case Type.ListOf(Type.TupleOf(List<Type> pair)) when pair.size() == 2 ->
                        element + " -> {\n    let (" + keyOf(container) + ", _) = " + element
                                + "\n    " + body + "\n}";
                default -> element + " -> " + body;
            };
        }

        /** The container at {@code container}, as a list of what it holds. */
        private String listed(Slot container) {
            String named = named(container);
            return switch (typeOf(container)) {
                case Type.ListOf _ -> named;
                case Type.SetOf _ -> "Set.toList(" + named + ")";
                case Type.MapOf _ -> "Map.toList(" + named + ")";
                case Type.OptionOf _ -> "Option.withDefault([], Option.map(o" + word(container)
                        + " -> [o" + word(container) + "], " + named + "))";
                default -> throw new IllegalStateException("no element of a "
                        + Type.show(typeOf(container)));
            };
        }

        private String subject(LawSubject<Slot> subject) {
            return switch (subject) {
                case LawSubject.Argument<Slot>(Slot at) -> named(at);
                case LawSubject.ElementOf<Slot>(Slot at) -> elementOf(at);
                // The closure's body over what it is handed, which is the element where it
                // stands.
                case LawSubject.WhatTheClosureAnswers<Slot>(Slot at) -> {
                    Slot container = within.getLast();
                    String closure = closures.get(((Slot.Place) at).position());
                    String body = closure.substring(closure.indexOf("->") + 2).strip();
                    yield "(" + body.replaceAll("\\bv\\b", elementOf(container))
                            .replaceAll("\\bk\\b", keyOf(container)) + ")";
                }
                case LawSubject.KeyOf<Slot>(Slot at) -> keyOf(at);
                case LawSubject.AnswerOf<Slot>(var operation, var args) -> args.isEmpty()
                        ? operation.qualified()
                        : operation.qualified() + "(" + String.join(", ",
                                args.stream().map(this::subject).toList()) + ")";
            };
        }

        /** The type of {@code subject}, or null where it names a value of no type read yet. */
        Type typeOf(LawSubject<Slot> subject) {
            return switch (subject) {
                case LawSubject.Argument<Slot>(Slot at) -> typeOf(at);
                case LawSubject.ElementOf<Slot>(Slot at) -> typeOf(at) == null ? null
                        : switch (typeOf(at)) {
                            case Type.ListOf(Type element) -> element;
                            case Type.SetOf(Type element) -> element;
                            case Type.OptionOf(Type element) -> element;
                            case Type.MapOf(Type _, Type value) -> value;
                            default -> throw new IllegalStateException("no element of "
                                    + Type.show(typeOf(at)));
                        };
                case LawSubject.WhatTheClosureAnswers<Slot>(Slot at) ->
                        ((Type.FnOf) typeOf(at)).result();
                case LawSubject.KeyOf<Slot>(Slot at) ->
                        typeOf(at) == null ? null : Type.keyOf(typeOf(at));
                case LawSubject.AnswerOf<Slot>(var operation, var _) -> {
                    Stdlib.Signature declaration =
                            DefaultStdlib.get().entry(operation).signature();
                    yield instantiated(List.of(declaration.result()), declaration).getFirst();
                }
            };
        }

        private static String whole(ExactRatio ratio) {
            if (!ratio.isWhole()
                    || !(ratio.floor() instanceof ExactAnswer.Held<BigInteger>(BigInteger whole))) {
                throw new IllegalStateException("a statement over whole numbers is written in"
                        + " them");
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
