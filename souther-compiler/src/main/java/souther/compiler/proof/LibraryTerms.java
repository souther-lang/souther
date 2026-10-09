package souther.compiler.proof;

import souther.compiler.ast.Hir;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.BindingId;
import souther.compiler.types.ReachName;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

/**
 * A library operation's body read into a {@link LibraryTerm}.
 *
 * <p>Where the library's resolved tree is read for what an operation keeps. Names are already
 * resolved there, so a parameter and a binding are told apart by what they reach and never by how
 * they are written; a sugar is rewritten as the library rewrites it everywhere else. The walk's own
 * body is read where the library is built ({@code core.TheWalk}), since an output lowers it from
 * there, and what is read here takes the walk as that reading found it.
 */
public final class LibraryTerms {

    private final Stdlib library;
    private final List<BindingId> params;

    private LibraryTerms(Stdlib library, List<BindingId> params) {
        this.library = library;
        this.params = params;
    }

    /** The body of {@code declaration}, a declaration of {@code library} written in the language. */
    public static LibraryTerm of(Stdlib library, Hir.FnDef declaration) {
        if (!(declaration.body() instanceof Hir.FnBody.Written(Hir.Expr body))) {
            throw new IllegalArgumentException(declaration.written() + " has no body to read");
        }
        List<BindingId> params = new ArrayList<>();
        declaration.params().forEach(p -> params.add(p.binder().binding()));
        return new LibraryTerms(library, List.copyOf(params)).read(body);
    }

    private LibraryTerm read(Hir.Expr e) {
        return switch (e) {
            case Hir.Var var -> named(var);
            case Hir.IntLit lit -> new LibraryTerm.WholeNumber(lit.value());
            case Hir.DecimalLit lit -> new LibraryTerm.DecimalNumber(lit.value());
            case Hir.BoolLit lit -> new LibraryTerm.Truth(lit.value());
            case Hir.Neg neg -> new LibraryTerm.Negated(read(neg.operand()));
            case Hir.ListLit list -> new LibraryTerm.ListOf(all(list.elements()));
            case Hir.Tuple tuple -> new LibraryTerm.TupleOf(all(tuple.elements()));
            case Hir.TupleGet get -> new LibraryTerm.Component(read(get.tuple()), get.index());
            case Hir.Binary binary -> new LibraryTerm.Operator(binary.op(), read(binary.left()),
                    read(binary.right()), binary.origin());
            case Hir.If fork -> new LibraryTerm.Fork(read(fork.cond()), read(fork.then()),
                    read(fork.els()), fork.origin());
            case Hir.LetIn let -> new LibraryTerm.Let(let.binder().binding(), read(let.value()),
                    read(let.body()));
            case Hir.Block block -> {
                List<BindingId> bound = new ArrayList<>();
                block.params().forEach(p -> bound.add(p.binding()));
                yield new LibraryTerm.Closure(bound, read(block.body()));
            }
            case Hir.Apply apply -> applied(apply);
            case Hir.Match match -> onAnOption(match);
            case Hir.StringLit _ -> new LibraryTerm.Unread(LibraryTerm.Unwritten.A_STRING);
            case Hir.NewData _, Hir.FieldAccess _, Hir.IfConstructed _ ->
                    new LibraryTerm.Unread(LibraryTerm.Unwritten.A_DECLARED_VALUE);
            case Hir.ListComp _, Hir.RowCollection _ ->
                    new LibraryTerm.Unread(LibraryTerm.Unwritten.A_COMPREHENSION);
            case Hir.Unreachable _ ->
                    new LibraryTerm.Unread(LibraryTerm.Unwritten.AN_UNREACHABLE_PLACE);
            case Hir.Materialised _, Hir.ValueBuild _, Hir.ValueInvocation _, Hir.Expansion _ ->
                    new LibraryTerm.Unread(LibraryTerm.Unwritten.AN_EXPANSION);
        };
    }

    private List<LibraryTerm> all(List<Hir.Expr> each) {
        List<LibraryTerm> out = new ArrayList<>();
        each.forEach(e -> out.add(read(e)));
        return out;
    }

    /** What a name reaches: a parameter of the operation, or something bound inside its body. */
    private LibraryTerm named(Hir.Var var) {
        if (var.answered() == null) {
            return new LibraryTerm.Unread(LibraryTerm.Unwritten.A_NAME_OF_NOTHING_HERE);
        }
        return switch (var.answered().reachedAs()) {
            case ReachName.InScope(ValueName.Local local) -> {
                int position = params.indexOf(local.id());
                yield position >= 0 ? new LibraryTerm.Parameter(position)
                        : new LibraryTerm.Bound(local.id());
            }
            // A declaration with no parameters is a value, and reading its name is reading what it
            // answers; one with parameters, named and not applied, is handed over as a function.
            case ReachName.OfLibrary(var operation) ->
                    library.entry(operation).signature().params().isEmpty()
                            ? new LibraryTerm.Call(operation, List.of())
                            : new LibraryTerm.Unread(LibraryTerm.Unwritten.AN_OPERATION_AS_A_VALUE);
            case ReachName.InScope _, ReachName.Own _, ReachName.OfModule _,
                 ReachName.TheNamespace _ ->
                    new LibraryTerm.Unread(LibraryTerm.Unwritten.A_NAME_OF_NOTHING_HERE);
        };
    }

    /** An application: of a library operation, through the rewrite a sugar is, or of a closure. */
    private LibraryTerm applied(Hir.Apply apply) {
        List<LibraryTerm> args = all(apply.args());
        if (apply.function() instanceof Hir.Var var && var.answered() != null
                && var.answered().reachedAs() instanceof ReachName.OfLibrary(var operation)) {
            Stdlib.Rewrite rewrite = library.rewrites().get(operation);
            return rewrite == null ? new LibraryTerm.Call(operation, args)
                    : new LibraryTerm.Call(rewrite.target(),
                            rewrite.arguments(args, LibraryTerm.WholeNumber::new));
        }
        return new LibraryTerm.Applied(read(apply.function()), args);
    }

    /** A match, where it is one on whether an option holds a value. */
    private LibraryTerm onAnOption(Hir.Match match) {
        Hir.Case present = null;
        Hir.Case absent = null;
        for (Hir.Case arm : match.cases()) {
            TypeSymbol taken = arm.caseTypes().size() == 1
                    && arm.caseTypes().get(0).answered() != null
                    ? arm.caseTypes().get(0).answered().type() : null;
            if (TypeSymbol.SOME.equals(taken) && present == null && arm.binding() != null) {
                present = arm;
            } else if (TypeSymbol.NONE.equals(taken) && absent == null) {
                absent = arm;
            } else {
                return new LibraryTerm.Unread(LibraryTerm.Unwritten.A_MATCH_ON_DECLARED_CASES);
            }
        }
        if (present == null || absent == null) {
            return new LibraryTerm.Unread(LibraryTerm.Unwritten.A_MATCH_ON_DECLARED_CASES);
        }
        return new LibraryTerm.OnAnOption(read(match.scrutinee()), present.binding().binding(),
                read(present.body()), read(absent.body()), match.origin());
    }
}
