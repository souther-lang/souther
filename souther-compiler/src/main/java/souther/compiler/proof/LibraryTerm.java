package souther.compiler.proof;

import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.util.List;
import java.util.Objects;

/**
 * A library operation's body as the rules here read it: what it applies, binds and chooses
 * between, with every name resolved to what it is.
 *
 * <p>Read once off the tree the library was resolved into ({@link LibraryTerms}), so a rule asks
 * what a term is and never how it was spelled. A sugar is already the call it stands for, and a
 * tuple bound by a pattern is already the component it reads. What the reading has no word for is
 * {@link Unread}, and a rule meeting one reads no further.
 */
public sealed interface LibraryTerm {

    /** The operation's own parameter at {@code position}. */
    record Parameter(int position) implements LibraryTerm {}

    /** A value bound inside the body: a closure's parameter, a {@code let}, an arm's payload. */
    record Bound(BindingId binding) implements LibraryTerm {}

    /** A whole number written out. */
    record WholeNumber(long value) implements LibraryTerm {}

    /** A decimal written out. */
    record DecimalNumber(BigDecimal value) implements LibraryTerm {}

    /** A truth written out. */
    record Truth(boolean value) implements LibraryTerm {}

    /** A list written out, element by element. */
    record ListOf(List<LibraryTerm> elements) implements LibraryTerm {

        public ListOf {
            elements = List.copyOf(elements);
        }
    }

    /** A tuple written out. */
    record TupleOf(List<LibraryTerm> elements) implements LibraryTerm {

        public TupleOf {
            elements = List.copyOf(elements);
        }
    }

    /** The component at {@code index} of a tuple. */
    record Component(LibraryTerm tuple, int index) implements LibraryTerm {}

    /** A library operation applied, with the arguments it takes — a sugar's supplied ones included. */
    record Call(ValueName.Stdlib.Operation operation, List<LibraryTerm> args) implements LibraryTerm {

        public Call {
            Objects.requireNonNull(operation, "a call is of an operation");
            args = List.copyOf(args);
        }
    }

    /** A closure applied: a parameter or a bound value that is a function. */
    record Applied(LibraryTerm function, List<LibraryTerm> args) implements LibraryTerm {

        public Applied {
            args = List.copyOf(args);
        }
    }

    /** A closure written out. */
    record Closure(List<BindingId> params, LibraryTerm body) implements LibraryTerm {

        public Closure {
            params = List.copyOf(params);
        }
    }

    /** {@code value} bound to {@code binding} for {@code body}. */
    record Let(BindingId binding, LibraryTerm value, LibraryTerm body) implements LibraryTerm {}

    /** A fork on a truth, written at {@code origin}. */
    record Fork(LibraryTerm condition, LibraryTerm then, LibraryTerm otherwise,
                SourceConstructOrigin origin) implements LibraryTerm {}

    /**
     * A match on whether an option holds a value, written at {@code origin}: {@code present} with
     * the value bound to {@code value}, {@code absent} otherwise.
     */
    record OnAnOption(LibraryTerm option, BindingId value, LibraryTerm present, LibraryTerm absent,
                      SourceConstructOrigin origin) implements LibraryTerm {}

    /** One of the language's own operators applied to two values, written at {@code origin}. */
    record Operator(BinOp op, LibraryTerm left, LibraryTerm right, SourceConstructOrigin origin)
            implements LibraryTerm {}

    /** A number negated. */
    record Negated(LibraryTerm operand) implements LibraryTerm {}

    /** Something this reading has no word for, and which kind of thing it was. */
    record Unread(Unwritten what) implements LibraryTerm {}

    /** The kinds of thing a body may hold that no rule here reads. */
    enum Unwritten {
        /** A string written out. */
        A_STRING,
        /** A value of a declared type built, or a field of one read. */
        A_DECLARED_VALUE,
        /** A match on the cases of a type other than an option. */
        A_MATCH_ON_DECLARED_CASES,
        /** A form the tree takes only after a body is expanded into another. */
        AN_EXPANSION,
        /** A comprehension, or a collection of rows. */
        A_COMPREHENSION,
        /** A place a run never reaches. */
        AN_UNREACHABLE_PLACE,
        /** A name that reaches nothing a body of the library can bind. */
        A_NAME_OF_NOTHING_HERE,
        /** An operation handed over as a value rather than applied. */
        AN_OPERATION_AS_A_VALUE
    }
}
