package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * What the invariant-discharge check names a value by — the identity two writings of one value
 * share, and the whole of what a fact set knows about which value it is talking about.
 *
 * <p>A value, not a rendering of one. Two terms are the same term when they are built the same way
 * out of the same parts, and that is the only thing that makes them the same. This was a string
 * before, written by concatenating the parts' own strings, and the encoding was not injective: a
 * list of one string element {@code a", "b} and a list of two elements {@code ["a", "b"]} wrote one
 * key, so a guard about the first discharged a clause about the second. Nothing here can spell one
 * value the way another spells itself, because nothing here spells anything.
 *
 * <p>Equality is structural. {@link Terms} hands every term it builds through an interner, so two
 * writings of one value are usually one object and the comparison stops at the first line — but that
 * is an optimisation and not the contract. A term built without going through that interner, or
 * through another one, is equal to its twin all the same, which is what lets one reading be compared
 * against another.
 *
 * <p>The hash is computed once, when the term is built, out of the hashes its parts already carry.
 * A chain of terms is a graph and not a tree — a name read twice is one value read twice — so a hash
 * that walked the parts at every ask would cost what writing the parts out used to cost, which is
 * the thing that made the string form of this hold a name for each shape rather than the shape.
 *
 * <p>Equality of an {@code ==} between two values does not depend on which was written first, so
 * that shape holds its two parts as a pair with no order. Every other shape is ordered.
 */
final class Term {

    /** How a term is built. What a shape means is what {@link Terms} builds it for; this says only
     * which shapes are told apart. */
    enum Shape {
        /** A place: a binding and the fields read from it. */
        AT,
        /** A parameter of a closure, named by where it is bound rather than by which binding it is. */
        BOUND,
        /** Fields read off a term that is not a place. */
        ON,
        INT, DECIMAL, STRING, BOOL, UNIT,
        /** Arithmetic negation. */
        NEG,
        /** The denial of a condition. */
        NOT,
        /** An {@code ==}, whose two parts are unordered. */
        EQ,
        /** Any other operator, over its two operands in the order written. */
        OP,
        LIST, TUPLE,
        /** One element of a tuple, by index. */
        PART,
        /** A conditional, over its condition and its two branches. */
        CHOICE,
        /** A closure, over the number of parameters it binds and its body. */
        CLOSURE,
        /** A value bound and a body read under it. */
        LET,
        /** A construction, over the values its fields are given in declaration order. */
        BUILT,
        /** A call the representation kept standing, over its arguments. */
        CALLED
    }

    /** What a shape holds beside its parts: a location, a written value, an operator, the name of an
     * operation, the type and fields of a construction. Compared by its own equality. */
    private final Object of;
    private final Shape shape;
    private final List<Term> parts;
    private final int hash;

    /**
     * How a term's hash is mixed with the hashes of its parts.
     *
     * <p>An odd number, and not a small one. A term that reads one part twice folds that part in
     * twice, so the multiplier decides what a chain of those does to the hash it carries up: with
     * {@code 31}, a part folded twice contributes {@code 32} times what the level under it did, and
     * thirty-two is two to the fifth — seven links of that shift every bit of the hash out, and from
     * there every link of the chain hashes alike. The chain is exactly what {@link Terms} builds when
     * a body names a value and reads it twice, so the terms that collided were the ones the sharing
     * is for.
     */
    private static final int MIX = 0x9E3779B1;

    private Term(Shape shape, Object of, List<Term> parts) {
        this.shape = shape;
        this.of = of;
        this.parts = List.copyOf(parts);
        int h = shape.hashCode() * MIX + (of == null ? 0 : of.hashCode());
        h = h * MIX + this.parts.size();
        if (shape == Shape.EQ) {
            // an equality is between two values and not from one to the other
            h = h * MIX + (this.parts.get(0).hash + this.parts.get(1).hash);
        } else {
            for (Term part : this.parts) {
                h = h * MIX + part.hash;
            }
        }
        // A last mix, so that what a level carries up depends on its high bits as well as its low
        // ones: without it a hash the multiplier only ever shifts left says less the deeper it goes.
        this.hash = h ^ (h >>> 16);
    }

    Shape shape() {
        return shape;
    }

    @Override
    public int hashCode() {
        return hash;
    }

    @Override
    public boolean equals(Object other) {
        if (this == other) {
            return true;
        }
        if (!(other instanceof Term term) || term.hash != hash || term.shape != shape
                || !java.util.Objects.equals(term.of, of)) {
            return false;
        }
        if (shape == Shape.EQ) {
            return (parts.get(0).equals(term.parts.get(0)) && parts.get(1).equals(term.parts.get(1)))
                    || (parts.get(0).equals(term.parts.get(1))
                            && parts.get(1).equals(term.parts.get(0)));
        }
        return parts.equals(term.parts);
    }

    /**
     * How this reads where a person is shown one — a report, a log, this compiler's own tests.
     *
     * <p>What it renders as says nothing about what it is. Two terms rendering alike are not thereby
     * one term, and nothing here reads a rendering back: that is what the string form of this was,
     * and it is why an escaping bug in it could make one value out of two.
     */
    String rendered() {
        StringBuilder sb = new StringBuilder();
        switch (shape) {
            case AT, BOUND -> sb.append(of);
            case ON -> sb.append(parts.get(0).rendered()).append(path());
            case INT, DECIMAL, BOOL -> sb.append(of);
            case STRING -> sb.append('"').append(of).append('"');
            case UNIT -> sb.append(of);
            case NEG -> sb.append('-').append(parts.get(0).rendered());
            case NOT -> sb.append('!').append(parts.get(0).rendered());
            case EQ -> sb.append('(').append(parts.get(0).rendered()).append(" == ")
                    .append(parts.get(1).rendered()).append(')');
            case OP -> sb.append('(').append(parts.get(0).rendered()).append(' ').append(of)
                    .append(' ').append(parts.get(1).rendered()).append(')');
            case LIST -> joined(sb.append('['), ", ").append(']');
            case TUPLE -> joined(sb.append('('), ", ").append(')');
            case PART -> sb.append(parts.get(0).rendered()).append('.').append(of);
            case CHOICE -> joined(sb.append("if("), ", ").append(')');
            case CLOSURE -> joined(sb.append("\\").append(of).append('('), ", ").append(')');
            case LET -> joined(sb.append("let("), ", ").append(')');
            case BUILT -> {
                Built built = (Built) of;
                sb.append(built.type()).append('{');
                for (int i = 0; i < parts.size(); i++) {
                    sb.append(i == 0 ? "" : ", ").append(built.fields().get(i)).append('=')
                            .append(parts.get(i).rendered());
                }
                sb.append('}');
            }
            case CALLED -> joined(sb.append(((ValueName) of).name()).append('('), ", ").append(')');
        }
        return sb.toString();
    }

    private StringBuilder joined(StringBuilder sb, String between) {
        for (int i = 0; i < parts.size(); i++) {
            sb.append(i == 0 ? "" : between).append(parts.get(i).rendered());
        }
        return sb;
    }

    private String path() {
        StringBuilder sb = new StringBuilder();
        for (String field : fields()) {
            sb.append('.').append(field);
        }
        return sb.toString();
    }

    @Override
    public String toString() {
        return rendered();
    }

    /** The type a construction builds and the fields it gives values to, in the order the parts hold
     * those values. */
    record Built(TypeSymbol type, List<String> fields) {

        Built {
            fields = List.copyOf(fields);
        }
    }

    /** Where a closure's parameter is bound: which closure down from here, and which parameter. */
    record At(int depth, int index) {

        @Override
        public String toString() {
            return "#" + depth + "." + index;
        }
    }

    @SuppressWarnings("unchecked")
    private List<String> fields() {
        return (List<String>) of;
    }

    // --- how terms are built -------------------------------------------------------------------

    /**
     * Terms this analysis has built, each under the one instance of it that stands for it.
     *
     * <p>Sharing, not identity. Two writings of one value are equal terms whether or not they were
     * built here; going through this makes the comparison stop at the first line and makes the hash
     * a term already carries the one its parts are hashed from. One of these lives as long as the
     * reading that fills it.
     */
    static final class Interner {

        private final Map<Term, Term> shared = new HashMap<>();

        private Term of(Shape shape, Object of, List<Term> parts) {
            Term made = new Term(shape, of, parts);
            Term had = shared.putIfAbsent(made, made);
            return had != null ? had : made;
        }

        /** The place {@code where} is. */
        Term at(Location where) {
            return of(Shape.AT, where, List.of());
        }

        /** A closure's parameter, by where it is bound. */
        Term bound(int depth, int index) {
            return of(Shape.BOUND, new At(depth, index), List.of());
        }

        /**
         * {@code base} with {@code fields} read off it, or {@code base} where none are.
         *
         * <p>One chain and not a chain of chains: fields read off something that already has fields
         * read off it are the one path, so a value reached a field at a time and the same value
         * reached all at once are one term.
         */
        Term on(Term base, List<String> fields) {
            if (fields.isEmpty()) {
                return base;
            }
            if (base.shape == Shape.ON) {
                List<String> whole = new ArrayList<>(base.fields());
                whole.addAll(fields);
                return of(Shape.ON, List.copyOf(whole), base.parts);
            }
            return of(Shape.ON, List.copyOf(fields), List.of(base));
        }

        Term written(long value) {
            return of(Shape.INT, value, List.of());
        }

        Term written(BigDecimal value) {
            return of(Shape.DECIMAL, value, List.of());
        }

        Term written(String value) {
            return of(Shape.STRING, value, List.of());
        }

        Term written(boolean value) {
            return of(Shape.BOOL, value, List.of());
        }

        Term unit(TypeSymbol data) {
            return of(Shape.UNIT, data, List.of());
        }

        Term negated(Term operand) {
            return of(Shape.NEG, null, List.of(operand));
        }

        /** The denial of {@code condition}, and of a denial the condition itself. */
        Term not(Term condition) {
            return condition.shape == Shape.NOT ? condition.parts.get(0)
                    : of(Shape.NOT, null, List.of(condition));
        }

        /**
         * The operator over its two operands.
         *
         * <p>Six comparisons are three: {@code >} is {@code <} the other way round, and {@code >=}
         * and {@code <=} are the denials of the other two. So two clauses comparing the same two
         * terms are one term however the author reached for it, which matters wherever the
         * comparison is not the whole condition — only there can the denial not be carried by the
         * polarity instead.
         */
        Term operator(Hir.BinOp op, Term left, Term right) {
            return switch (op) {
                case EQ -> of(Shape.EQ, null, List.of(left, right));
                case NE -> not(of(Shape.EQ, null, List.of(left, right)));
                case LT -> of(Shape.OP, Hir.BinOp.LT, List.of(left, right));
                case GT -> of(Shape.OP, Hir.BinOp.LT, List.of(right, left));
                case GE -> not(of(Shape.OP, Hir.BinOp.LT, List.of(left, right)));
                case LE -> not(of(Shape.OP, Hir.BinOp.LT, List.of(right, left)));
                default -> of(Shape.OP, op, List.of(left, right));
            };
        }

        Term list(List<Term> elements) {
            return of(Shape.LIST, null, elements);
        }

        Term tuple(List<Term> elements) {
            return of(Shape.TUPLE, null, elements);
        }

        Term part(Term tuple, int index) {
            return of(Shape.PART, index, List.of(tuple));
        }

        Term choice(Term condition, Term then, Term els) {
            return of(Shape.CHOICE, null, List.of(condition, then, els));
        }

        Term closure(int params, Term body) {
            return of(Shape.CLOSURE, params, List.of(body));
        }

        Term let(Term value, Term body) {
            return of(Shape.LET, null, List.of(value, body));
        }

        /** A construction, over what each field is given in declaration order. */
        Term built(TypeSymbol type, List<String> fields, List<Term> values) {
            return of(Shape.BUILT, new Built(type, fields), values);
        }

        /** A call to {@code operation} over its arguments — which is what a size taken of a container
         * is, so a guard's size and a clause's size meet as one value rather than as two spellings
         * that have to keep agreeing. */
        Term called(ValueName operation, List<Term> args) {
            return of(Shape.CALLED, operation, args);
        }

        /**
         * The call {@code operation} over {@code args} where this has built one before, and null
         * where it has not.
         *
         * <p>Recognised and not made. A reader asking what was said about a size wants the term a
         * clause already named it by; answering with a fresh one would put a term nothing has spoken
         * about where an answer was expected.
         */
        Term calledIfBuilt(ValueName operation, List<Term> args) {
            Term made = new Term(Shape.CALLED, operation, args);
            return shared.containsKey(made) ? made : null;
        }

        /** How many distinct terms this has been asked for — what a test measuring the sharing
         * reads. */
        int size() {
            return shared.size();
        }
    }

    /** The parts, for a reader that walks one. */
    List<Term> parts() {
        return parts;
    }

    /**
     * How many distinct terms this one is made of, itself among them — what the representation of it
     * costs.
     *
     * <p>Counted rather than written out. A term is a graph and not a tree: a name read twice is one
     * value read twice, so writing out what a term holds writes a part once per path to it, and a
     * chain of them doubles per link. Held once and read from two places, a link costs a link.
     */
    int distinct() {
        java.util.Set<Term> seen = java.util.Collections.newSetFromMap(new java.util.IdentityHashMap<>());
        java.util.Deque<Term> left = new java.util.ArrayDeque<>(List.of(this));
        while (!left.isEmpty()) {
            Term term = left.pop();
            if (seen.add(term)) {
                left.addAll(term.parts);
            }
        }
        return seen.size();
    }
}
