package souther.compiler.check;

import souther.compiler.types.BinOp;
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
        /** A call, over its arguments. */
        CALLED,
        /**
         * One evaluation, told apart from every other by the { EvaluationId} it holds and not by
         * anything about its shape.
         *
         * <p>The one nominal atom. Everything else here is structural all the way down, which is what
         * makes two writings of one value one term; a value nothing may share needs a leaf that is
         * equal to nothing but itself, and it needs to be a leaf of this same algebra so that what is
         * built over it composes. { length(E)} written twice is one term because { CALLED}
         * interns over its children and the child is the one atom both times.
         */
        EVALUATION,
        /** A value given to an optional position. */
        SOME,
        /**
         * What a present optional holds, read where an arm has opened one.
         *
         * <p>The one operation that takes a value apart here, and it is not a projection algebra: an
         * optional's carrier is the only case whose binding is a different value from the value it was
         * read out of, so this is that one case and nothing more general. Everything else a
         * {@code match} opens binds the value it was given.
         */
        HELD,
        /** The empty optional, at the type of the position it fills. */
        NONE,
        /**
         * A value a walk hands its step, read where that walk is being proved about.
         *
         * <p>Named against the walk and by which parameter it arrives on, because that is what makes
         * it one value. The step's parameters are bindings, and two readings of one walk bind them
         * twice — a walk is keyed by what it is written over, with the step's binders normalised, so
         * the very same walk arrives with different bindings and is one atom. An accumulator named by
         * its binding was then two values under one name, which is what the check refuses to hold.
         *
         * <p>And by the walk, not only by the position: two walks in one body each hand their step an
         * accumulator, and they are two values.
         */
        HANDED,
        /** A value opened, over the scrutinee and each arm's body. */
        MATCHED,
        /** An attempted construction, over what it builds and what each of its departures answers. */
        ATTEMPTED
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
     * Whether this stands on one evaluation and nothing else this check can read — the atom itself,
     * or a field read off one.
     *
     * <p>Such a term names a value, which is what lets a guard or a declaration speak about it; it
     * says nothing at all on its own. The two used to be one answer, because a value with no
     * structure to read had no name either, and a reader could take having a name as evidence that
     * something was readable. Now it is not evidence, and the readers that used it that way ask this.
     */
    boolean standsOnAnEvaluation() {
        return switch (shape) {
            case EVALUATION -> true;
            case ON, HELD, HANDED -> parts.get(0).standsOnAnEvaluation();
            default -> false;
        };
    }

    String rendered() {
        StringBuilder sb = new StringBuilder();
        switch (shape) {
            case AT, BOUND -> sb.append(of);
            case EVALUATION -> sb.append(of);
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
            case SOME -> sb.append("Some(").append(parts.get(0).rendered()).append(')');
            case HELD -> sb.append("held(").append(parts.get(0).rendered()).append(')');
            case HANDED -> sb.append("handed(").append(parts.get(0).rendered()).append(", ")
                    .append(of).append(')');
            case NONE -> sb.append("None:").append(of);
            case MATCHED -> joined(sb.append("match("), ", ").append(')');
            case ATTEMPTED -> joined(sb.append("attempt("), ", ").append(')');
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

    /**
     * How this reads where a person is shown one — a report, a log, this compiler's own tests.
     *
     * <p>What it renders as says nothing about what it is. Two terms rendering alike are not thereby
     * one term, and nothing here reads a rendering back: that is what the string form of this was,
     * and it is why an escaping bug in it could make one value out of two.
     */
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
         *
         * <p>Which holds of a place too. A place is a root and the fields read from it ({@link
         * Shape#AT}), so reading one more field off it is that same root with a longer path, and not
         * a path over a term that happens to be a place. Reading a value's fields does not decide
         * which value it is, so the two spellings of {@code x.a} — the whole chain asked at once, and
         * {@code a} read off what {@code x} is — are one term. Without it a reader that builds a
         * chain from the root's own identity and a reader that builds it from the location answer
         * differently about one value, which is the identity question given two authorities.
         */
        Term on(Term base, List<String> fields) {
            if (fields.isEmpty()) {
                return base;
            }
            if (base.shape == Shape.AT) {
                Location where = (Location) base.of;
                List<String> whole = new ArrayList<>(where.path());
                whole.addAll(fields);
                return at(new Location(where.root(), whole));
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
        Term operator(BinOp op, Term left, Term right) {
            return switch (op) {
                case EQ -> of(Shape.EQ, null, List.of(left, right));
                case NE -> not(of(Shape.EQ, null, List.of(left, right)));
                case LT -> of(Shape.OP, BinOp.LT, List.of(left, right));
                case GT -> of(Shape.OP, BinOp.LT, List.of(right, left));
                case GE -> not(of(Shape.OP, BinOp.LT, List.of(left, right)));
                case LE -> not(of(Shape.OP, BinOp.LT, List.of(right, left)));
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

        /** The value one evaluation answered. Equal to itself and to nothing else, because an
         * { EvaluationId} is. */
        Term evaluated(EvaluationId where) {
            return of(Shape.EVALUATION, where, List.of());
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

        /** A value given to an optional position. */
        Term some(Term value) {
            return of(Shape.SOME, null, List.of(value));
        }

        /**
         * What the present optional {@code optional} holds.
         *
         * <p>What a value was built out of is what taking it apart answers: an optional written as
         * {@code Some(v)} holds {@code v}, so opening it names {@code v} and not a value of its own.
         * Stated here beside the building of it, because a constructor and what undoes it are one
         * fact and holding them apart is holding it twice.
         */
        Term held(Term optional) {
            if (optional.shape == Shape.SOME) {
                return optional.parts.get(0);
            }
            return of(Shape.HELD, null, List.of(optional));
        }

        /** What the walk {@code walk} hands its step on parameter {@code param}. */
        Term handed(Term walk, int param) {
            return of(Shape.HANDED, param, List.of(walk));
        }

        /** The empty optional. Held at the type of the position, since the absent value of one
         * optional is not the absent value of another. */
        Term none(souther.compiler.types.Type type) {
            return of(Shape.NONE, type, List.of());
        }

        /** A value opened: the scrutinee, and what each arm answers, under the cases that arm takes.
         * An arm's binding is a parameter of the arm, keyed by where it is bound as a closure's is. */
        Term matched(Term scrutinee, List<List<TypeSymbol>> cases, List<Term> arms) {
            List<Term> parts = new ArrayList<>();
            parts.add(scrutinee);
            parts.addAll(arms);
            return of(Shape.MATCHED, List.copyOf(cases), parts);
        }

        /** An attempted construction: what it builds, what its success answers, and what each of its
         * departures answers, under the clauses those departures name. */
        Term attempted(Term built, List<String> clauses, List<Term> answers) {
            List<Term> parts = new ArrayList<>();
            parts.add(built);
            parts.addAll(answers);
            return of(Shape.ATTEMPTED, List.copyOf(clauses), parts);
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
