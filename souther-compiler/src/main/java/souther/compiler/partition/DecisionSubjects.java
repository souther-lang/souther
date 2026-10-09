package souther.compiler.partition;

import souther.compiler.check.AffineForms;
import souther.compiler.check.DeclarationAccess;
import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.DeclaredArgument;
import souther.compiler.check.Symbols;
import souther.compiler.numeric.LinearForm;
import souther.compiler.core.Core;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.InputTruth;
import souther.compiler.inputs.PathResolution;
import souther.compiler.inputs.ReadMeaning;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionArgument;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.InjectedAnswer;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * What a body's expressions name that a row can control.
 *
 * <p>One reading for every question the decision asks about a subject. A truth, a comparison and a
 * fork are three things to do with one of these, and each working out for itself what it was looking
 * at would be three accounts of one identity — after which a rule's columns could name two subjects
 * for one value and the table would admit an assignment the body never reaches.
 *
 * <p><b>Only what a row can control.</b> A position of the input is written at and an answer of a
 * dependency this behavior declares is stood in for. A call to anything else is a value the model
 * computes, and a row cannot be composed to make it come out one way rather than another. Which
 * calls are stood in for is the environment's to say ({@link InputReads#standsIn}), since it is a
 * fact about the body being read: a rule a declaration states is read where nothing is.
 */
record DecisionSubjects(InputDomain inputs, Symbols symbols, DeclarationAccess declarations,
                        DeclarationNewtypes newtypes) {

    DecisionSubjects {
        if (declarations == null || newtypes == null) {
            throw new IllegalArgumentException("reading what a row controls asks the declarations"
                    + " what they say, which form each of them is, which of them wrap one value"
                    + " and what each of those wraps, so it is handed somewhere to read every one"
                    + " of them");
        }
    }

    /**
     * What {@code e} names, or null where it is nothing a row controls.
     *
     * <p>The input is asked first, because a name that is a position is that position however it
     * was given its value. So is a name the cases of a sum share, which is no position and stands
     * at one under whichever case the row is: what the body decides on is the value at the name,
     * and a row controls it by what it writes under its case. What is left is read as an answer:
     * the fields taken off it, and under them a call this behavior stands a dependency in for.
     */
    DecisionSubject of(Core e, InputReads at) {
        if (at.pathOf(e, newtypes) instanceof PathResolution.At(TermPath stands)) {
            if (inputs.at(stands) != null) {
                return new DecisionSubject.AnInput(stands);
            }
            // Read at the sum, as a name on a value left several cases is.
            if (WhereANameIsWritten.ofAName(inputs, stands) != null) {
                return new DecisionSubject.AnInput(stands.position());
            }
        }
        return anAnswer(e, at);
    }

    /**
     * What a dependency answered, or a place inside it, that {@code e} is — or null where it is no
     * such thing.
     *
     * <p>The second half of {@link #of}, for a reader asking only this: what a position is takes
     * resolving where {@code e} stands, and which evaluation an answer is is
     * {@link InputReads#answerAt}'s. A newtype's value is the value it wraps, one subject and not a
     * step inside one: read as a step, {@code riskScore(c).value} and {@code riskScore(c)} would be
     * two columns over one answer.
     */
    DecisionSubject.AnAnswer anAnswer(Core e, InputReads at) {
        InputReads.AnAnswerAt found = at.answerAt(e, symbols, newtypes);
        if (found == null) {
            return null;
        }
        // What a report names the answer by is what it was asked about.
        List<DecisionArgument> arguments = new ArrayList<>();
        for (Core argument : found.arguments()) {
            arguments.add(argumentOf(argument, found.at()));
        }
        return new DecisionSubject.AnAnswer(new InjectedAnswer(found.evaluation(), arguments),
                found.steps());
    }

    /**
     * {@code truth} coming out {@code holding} as the truth of a subject a row controls, or null
     * where it is the truth of none.
     *
     * <p>Through what {@link InputTruth#asked} reads through — a {@code let}, a name, a denial — and
     * so the one way through them for a truth here as for a truth of a position. Read without it,
     * {@code Bool.not(known(name))} was no column, while the reading of the input, which looks
     * through the denial, found {@code known(name)} under it and handed it over: a condition both
     * readings let go.
     */
    DecidedCondition.Stood truthOf(Core truth, boolean holding, InputReads reads) {
        InputTruth.Asked asked = InputTruth.asked(truth, holding, reads, symbols, newtypes);
        DecisionSubject subject = of(asked.value(), asked.reads());
        return subject == null ? null : new DecidedCondition.Stood(
                new DecisionCondition.ATruth(subject), asked.holding());
    }

    /**
     * Whether {@code e} is a {@code Bool} whose truth, read as {@link #truthOf} reads it, is that of
     * what a dependency answered.
     *
     * <p>Only a truth. An answer that is a value inside a condition — compared, or handed to an
     * operation — is not what the condition decides.
     */
    boolean isTheTruthOfAnAnswer(Core e, InputReads reads) {
        DecidedCondition.Stood truth = Core.withoutStanding(e).type() == Type.Prim.BOOL
                ? truthOf(e, true, reads) : null;
        return truth != null && truth.condition().of() instanceof DecisionSubject.AnAnswer;
    }

    /**
     * What {@code e} asks the dependency about.
     *
     * <p>Something a row controls, or a number the model settles. The second is asked of the same
     * walk the arithmetic folds a call with, so an expression this compiler works out to a number
     * is the number it works out to — the question a body asks by writing it is the question it
     * asks by writing the answer. Anything else is a value the model works out, named by how
     * ({@link DecisionArgument.WorkedOut}).
     */
    private DecisionArgument argumentOf(Core e, InputReads at) {
        DecisionSubject stands = of(e, at);
        if (stands != null) {
            return new DecisionArgument.OfASubject(stands);
        }
        return AffineForms.outcome(e, at, aNumberAndNothingElse())
                instanceof AffineForms.Outcome.Composed<Void, InputReads>(LinearForm<Void> form)
                && form.coefs().isEmpty()
                ? new DecisionArgument.OfANumber(form.constant())
                : new DecisionArgument.WorkedOut(workedOut(e, at, new HashSet<>()));
    }

    /**
     * How {@code e}, read in {@code at}, is worked out: the expression, each name in it written as
     * what it stands for there — a subject a row controls as that subject, a name read through as
     * what it was given, one of several values as all of them, and one that stands for none of these
     * as itself.
     *
     * @param met the bindings already read through on the way here, so a name that came round to
     *            itself is written as itself
     */
    private String workedOut(Core standing, InputReads at, Set<BindingId> met) {
        Core e = Core.withoutStanding(standing);
        DecisionSubject subject = of(e, at);
        if (subject != null) {
            return subject.spelled();
        }
        Denotation taken = at.taken(e);
        if (taken != null) {
            return workedOut(taken.value(), taken.at(), met);
        }
        return switch (e) {
            case Core.Read name when met.add(name.binding()) ->
                    switch (at.meaningOf(name, symbols, newtypes)) {
                        case ReadMeaning.Through(Denotation denotes) ->
                                workedOut(denotes.value(), denotes.at(), met);
                        case ReadMeaning.OneOf(List<Denotation> values) -> {
                            List<String> each = new ArrayList<>();
                            values.forEach(value -> each.add(
                                    workedOut(value.value(), value.at(), new HashSet<>(met))));
                            yield "one of " + each;
                        }
                        case ReadMeaning.Position _, ReadMeaning.Element _,
                             ReadMeaning.Unknown _ -> name.name();
                    };
            case Core.Read name -> name.name();
            case Core.LetIn let -> workedOut(let.body(), at.and(let.binder(), let.value()), met);
            // A newtype made of one value is that value wearing a name.
            case Core.Construct construct when newtypes.of(construct.typeName().key())
                    && construct.values().size() == 1 ->
                    workedOut(construct.values().getFirst().value(), at, met);
            case Core.Int written -> Long.toString(written.value());
            case Core.Decimal written -> written.value().toPlainString();
            case Core.Str written -> '"' + written.value() + '"';
            case Core.Bool written -> Boolean.toString(written.value());
            case Core.Temporal written -> written.text();
            default -> {
                List<String> parts = new ArrayList<>();
                Core.forEachChild(e, child -> parts.add(workedOut(child, at, met)));
                yield what(e) + parts;
            }
        };
    }

    /** What kind of expression {@code e} is, or which operation it applies, as a word. */
    private static String what(Core e) {
        return switch (e) {
            case Core.Call call -> call.fn().rendered();
            case Core.PreservedCall call -> call.declared().operation().toString();
            case Core.Binary binary -> binary.op().toString();
            case Core.FieldAccess access -> "." + access.field();
            default -> e.getClass().getSimpleName();
        };
    }

    /**
     * The arithmetic with no atoms at all, which composes a number and nothing else.
     *
     * <p>The same walk a comparison is read with, asked for less: what a name denotes is the one
     * answer there is about a name, so a number reached through a binding is the number. Where it
     * meets anything the language does not settle, it stops and there is no number here.
     */
    private AffineForms.Reading<Void, InputReads> aNumberAndNothingElse() {
        return new AffineForms.Reading<Void, InputReads>() {

            @Override
            public Symbols symbols() {
                return symbols;
            }

            @Override
            public DeclarationAccess declarations() {
                return declarations;
            }

            @Override
            public LinearForm<Void> leafOf(Core node, InputReads at) {
                return null;
            }

            @Override
            public InputReads inside(Core.LetIn li, InputReads at) {
                return at.and(li.binder(), li.value());
            }

            @Override
            public AffineForms.ReadThrough<InputReads> readThrough(Core.Read read, InputReads at) {
                return NameAnswers.denoting(read, at, symbols, newtypes);
            }

            @Override
            public List<AffineForms.ReadThrough<InputReads>> alternativesOf(Core.Read read,
                                                                           InputReads at) {
                return NameAnswers.alternativesOf(read, at, symbols, newtypes);
            }

            @Override
            public AffineForms.ReadThrough<InputReads> taken(Core node, InputReads at) {
                return NameAnswers.taken(node, at);
            }

            @Override
            public LinearForm<DeclaredArgument> takenAsAForm(Core node, InputReads at) {
                return NameAnswers.takenAsAForm(node, at);
            }

            @Override
            public boolean readsThrough(Core.FieldAccess fa, InputReads at) {
                // A field of something is a place and not a number this settles. What the input's
                // own places are is the question above this one, asked first.
                return false;
            }
        };
    }
}
