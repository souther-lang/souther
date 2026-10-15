package souther.compiler.proof;

import souther.compiler.semantics.LawProposition;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * A value a library operation's body comes to, over its own arguments, as the proofs here read it.
 *
 * <p>Symbolic: an argument is an argument, what an operation answers is that operation applied to
 * what it was handed, and what a closure answers is that closure applied. Nothing is computed; what
 * is known of a value is what a law of whatever made it says, read where it is observed
 * ({@link Observing}).
 */
sealed interface Value {

    /** The operation's own argument at {@code position}. */
    record Argument(int position) implements Value {}

    /**
     * A value standing for any one of its kind, inside one proof: what a walk has carried so far,
     * the part of the list it has walked, the element it is handed next.
     *
     * @param id   which one, within the proof that made it
     * @param what what it stands for, for a reader of a proof
     */
    record Fresh(int id, String what) implements Value {}

    /** What {@code operation} answers handed {@code args}. */
    record Made(ValueName.Stdlib.Operation operation, List<Value> args) implements Value {

        public Made {
            Objects.requireNonNull(operation, "a value is made by an operation");
            args = List.copyOf(args);
        }
    }

    /** A whole number. */
    record Whole(long value) implements Value {}

    /** A decimal. */
    record Decimal(BigDecimal value) implements Value {}

    /** A truth. */
    record Truth(boolean value) implements Value {}

    /** A list written out. */
    record Listed(List<Value> elements) implements Value {

        public Listed {
            elements = List.copyOf(elements);
        }
    }

    /** A tuple written out. */
    record Tupled(List<Value> elements) implements Value {

        public Tupled {
            elements = List.copyOf(elements);
        }
    }

    /** The component at {@code index} of a tuple that is not written out. */
    record Component(Value tuple, int index) implements Value {}

    /** A closure applied: an argument that is one, or what one was bound to. */
    record AppliedTo(Value function, List<Value> args) implements Value {

        public AppliedTo {
            args = List.copyOf(args);
        }
    }

    /** A closure written in a body, with what the arguments of that body and the names around the
     *  closure were bound to. */
    record Lambda(LibraryTerm.Closure closure, List<Value> params, Map<BindingId, Value> around)
            implements Value {

        public Lambda {
            params = List.copyOf(params);
            around = Map.copyOf(around);
        }
    }

    /** A truth that is what {@code holds} says. */
    record Statement(LawProposition<Value> holds) implements Value {}

    /** Two numbers added or taken one from the other, or one negated where {@code left} is nought. */
    record Arithmetic(BinOp op, Value left, Value right) implements Value {}

    /** Two lists joined by the language's own operator. */
    record Joined(Value left, Value right) implements Value {}

    /** An element of {@code container}: the one a statement about some element of it is about. */
    record ElementOf(Value container) implements Value {}

    /** The key {@code element}, an element of a map, is filed under. */
    record KeyOf(Value element) implements Value {}

    /** The value an option holds, where it holds one. */
    record PayloadOf(Value option) implements Value {}

    /** The list {@code walked} with {@code next} after it: what a walk has walked one step on. */
    record OneMore(Value walked, Value next) implements Value {}

    /** The empty list a walk has walked before it starts. */
    record NothingYet() implements Value {}

    /**
     * A list of a map's entries, each a pair of its key and its value, read as the map they are the
     * entries of: what a walk over a map has walked, where a statement about the map's values each
     * under its key is about it.
     */
    record AsEntries(Value entries) implements Value {}
}
