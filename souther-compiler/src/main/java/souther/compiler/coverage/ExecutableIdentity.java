package souther.compiler.coverage;

import souther.compiler.core.Core;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;

/**
 * What a body does, written so that two compiles of one source write the same thing.
 *
 * <p>Beside the numbering rather than under it. A run is recorded in numbers, and a number means a
 * place only under the numbering that handed it out; holding one numbering against another needs
 * both what each number is an address of and what the code at those addresses does. This is the
 * second half: two numberings that address the same places in bodies that do different things are
 * not two views of one measurement.
 *
 * <p><b>What is taken out, and why each.</b> A position is where the source put a term and not what
 * the term says. A {@link souther.compiler.types.CoverageOrigin} counts the constructs of a source
 * from one end, so a clause gaining a line moves every ordinal below it. Which copy of a body a fork
 * stands in is where the fork is. And a binding is an owner and a count over that owner, both minted
 * as an expansion makes copies — so a name is written here as the place it is bound at
 * ({@link BinderAddress}), which is a fact about the body rather than about the run that built it.
 *
 * <p><b>What is kept.</b> Everything a run turns on: which node kind, the operator, the literal, the
 * type, the field, the case a pattern selects, what a call reaches, and the children in the order
 * the node holds them. A function value keeps how many names it takes, which is not a binder but is
 * part of what applying it does.
 *
 * <p><b>Open types are refused rather than normalised.</b> A metavariable belongs to the elaboration
 * that raised it and no body a run goes through holds one, so meeting one here means this was taken
 * over a tree that is not the tree that runs — and a reading that quietly stood in for it would say
 * two bodies are one on the strength of a name the compiler invented.
 */
record ExecutableIdentity(Kind kind, List<Object> settled, List<ExecutableIdentity> children) {

    /** Which node this is. Named rather than held as the class, so that what two of these compare
     *  is what they say and not which classes a loader happened to make. */
    enum Kind {
        INT, DECIMAL, STR, BOOL, TEMPORAL, READ, UNIT_VALUE, OPTION_NONE, UNREACHABLE, NEG,
        FIELD_ACCESS, BINARY, CALL, APPLY, IF, IF_CONSTRUCTED, LET_IN, BLOCK, LIST_LIT,
        OPTION_SOME, TUPLE, TUPLE_GET, CONSTRUCT, MATCH
    }

    ExecutableIdentity {
        settled = List.copyOf(settled);
        children = List.copyOf(children);
    }

    /**
     * What {@code body} does, {@code binders} saying where each name it reads is bound.
     *
     * <p>The children are walked in the order {@link CoreStructure} names the slots, which is the
     * order the node holds them. So the shape of this value is the shape of the body, and two
     * bodies that differ in which slot a term stands in differ here.
     */
    static ExecutableIdentity of(Core body, Binders binders) {
        List<Object> settled = new ArrayList<>();
        settled.add(open(body.type()));
        Kind kind = say(body, settled, binders);
        List<ExecutableIdentity> children = new ArrayList<>();
        for (CoreStructure.Child child : CoreStructure.childrenOf(body)) {
            children.add(of(child.node(), binders));
        }
        return new ExecutableIdentity(kind, settled, children);
    }

    /** Everything but the children and the type: what the node says on its own. */
    private static Kind say(Core e, List<Object> settled, Binders binders) {
        return switch (e) {
            case Core.Int it -> {
                settled.add(it.value());
                yield Kind.INT;
            }
            case Core.Decimal it -> {
                settled.add(it.value());
                yield Kind.DECIMAL;
            }
            case Core.Str it -> {
                settled.add(it.value());
                yield Kind.STR;
            }
            case Core.Bool it -> {
                settled.add(it.value());
                yield Kind.BOOL;
            }
            case Core.Temporal it -> {
                settled.add(it.kind());
                settled.add(it.text());
                yield Kind.TEMPORAL;
            }
            // The place the name is bound, never the name: two bodies alike but for what a `let`
            // spells do the same thing, and the id the compiler minted for it moves with the copy.
            case Core.Read it -> {
                settled.add(it.binding() == null ? null : binders.at(it.binding()));
                yield Kind.READ;
            }
            case Core.UnitValue it -> {
                settled.add(it.data());
                yield Kind.UNIT_VALUE;
            }
            case Core.OptionNone _ -> Kind.OPTION_NONE;
            case Core.Unreachable it -> {
                settled.add(it.reason());
                yield Kind.UNREACHABLE;
            }
            case Core.Neg _ -> Kind.NEG;
            case Core.FieldAccess it -> {
                settled.add(it.field());
                yield Kind.FIELD_ACCESS;
            }
            case Core.Binary it -> {
                settled.add(it.op());
                yield Kind.BINARY;
            }
            case Core.Call it -> {
                settled.add(it.fn());
                yield Kind.CALL;
            }
            // What an analysis kept standing, which the tree that runs holds none of. Reaching one
            // means this was taken over a tree nothing executes.
            case Core.PreservedCall it -> throw it.unexpectedIn("what a body does");
            case Core.Apply _ -> Kind.APPLY;
            case Core.If _ -> Kind.IF;
            // The words the author put the departures under. They are written in the source and a
            // report quotes them, so two bodies that name their ways out differently say different
            // things.
            case Core.IfConstructed it -> {
                it.els().forEach(arm -> settled.add(arm.clause()));
                yield Kind.IF_CONSTRUCTED;
            }
            case Core.LetIn _ -> Kind.LET_IN;
            // How many names it takes. Not a binder — those are where they are and are read as
            // places — but applying a function of two names to one is not what this does.
            case Core.Block it -> {
                settled.add(it.params().size());
                yield Kind.BLOCK;
            }
            case Core.ListLit _ -> Kind.LIST_LIT;
            case Core.OptionSome _ -> Kind.OPTION_SOME;
            case Core.Tuple _ -> Kind.TUPLE;
            case Core.TupleGet it -> {
                settled.add(it.index());
                settled.add(it.arity());
                yield Kind.TUPLE_GET;
            }
            case Core.Construct it -> {
                settled.add(it.typeName());
                it.values().forEach(value -> settled.add(value.field()));
                yield Kind.CONSTRUCT;
            }
            case Core.Match it -> {
                it.cases().forEach(one -> settled.add(one.pattern()));
                yield Kind.MATCH;
            }
        };
    }

    /**
     * {@code type}, where it is one a run can have.
     *
     * <p>Refused rather than stood in for. What is left open belongs to the elaboration that raised
     * it: a metavariable is named after the application that made it, and an inferred variable after
     * whatever the checker called it. Either is a name this compile invented, so two bodies holding
     * one would be compared on it.
     */
    private static Type open(Type type) {
        switch (type) {
            case null -> { }
            case Type.MetaVar it -> throw new IllegalStateException(
                    "a body that runs holds no metavariable: " + it);
            case Type.Var it -> {
                if (it.inferred()) {
                    throw new IllegalStateException(
                            "a body that runs holds no inferred type variable: " + it);
                }
            }
            // Inside as well as at the top: what is left open is left open wherever it stands, and
            // a list of them is as much a type no run has as one of them is.
            case Type.ListOf it -> open(it.element());
            case Type.SetOf it -> open(it.element());
            case Type.OptionOf it -> open(it.element());
            case Type.MapOf it -> {
                open(it.key());
                open(it.value());
            }
            case Type.TupleOf it -> it.elements().forEach(ExecutableIdentity::open);
            case Type.FnOf it -> {
                it.params().forEach(ExecutableIdentity::open);
                open(it.result());
            }
            default -> { }
        }
        return type;
    }
}
