package souther.compiler.partition;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.Choice;
import souther.compiler.check.ClauseName;
import souther.compiler.check.Comparison;
import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.ScopeStep;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.meaning.CasesOfAnAnswer;
import souther.compiler.meaning.Conclusion;
import souther.compiler.meaning.Derivation;
import souther.compiler.meaning.MeaningsOfABody;
import souther.compiler.meaning.WhyUnread;
import souther.compiler.semantics.ConditionJoin;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.ModelOccurrence;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.function.Supplier;

/**
 * What each condition of a body states, read off the tree where the language's operations stand
 * and filed under the construct of the model it is asked at ({@link MeaningsOfABody}).
 *
 * <p>Three places a truth is asked, because those are the three a reader of the tree that runs
 * takes one in at: a fork's condition, the left operand of a short-circuit, and a comparison whose
 * outcome a run records. And each arm of a fork that chooses its arm by no condition — a
 * {@code match}, an attempted construction — since entering one is a truth of its own. Each is read
 * where it stands — under the bindings, arms and closures above it — which is the one reading of
 * what it states ({@link Pullback}).
 */
public final class MeaningsOfABodyReading {

    private final Supplier<InputReading> reading;
    private final Symbols symbols;
    private final DeclarationNewtypes newtypes;
    private InputReading read;
    private final MeaningsOfABody.Filing filed = new MeaningsOfABody.Filing();
    /** Whether this walk is inside a closure applied more times than a condition is read on
     *  ({@link CompositionBudget#READINGS_OF_ONE_CONDITION}). */
    private boolean pastTheFigure;

    private MeaningsOfABodyReading(Supplier<InputReading> reading, Symbols symbols,
                                   DeclarationNewtypes newtypes) {
        this.reading = reading;
        this.symbols = symbols;
        this.newtypes = newtypes;
    }

    /**
     * What each condition of {@code analysis} states, its names read as {@code reads} has them.
     *
     * <p>The input is read where a condition is met and not before: a body with nothing to read
     * the meaning of asks nothing of the rules its input is read by, and an answer depending on
     * them would be worked out again whenever they are.
     */
    public static MeaningsOfABody of(AnalysisBody analysis, Supplier<InputReading> read,
                                     InputReads reads, Symbols symbols,
                                     DeclarationNewtypes newtypes) {
        MeaningsOfABodyReading reading = new MeaningsOfABodyReading(read, symbols, newtypes);
        reading.walk(analysis.core(), reads);
        return reading.filed.filed();
    }

    /**
     * Which case the behavior {@code analysis} is the body of answers, over its own parameters
     * ({@link CasesOfAnAnswer}), its names read as {@code reads} has them — read once, for every
     * call of it to put in what that call handed.
     *
     * @param parameters the names the body reads its parameters by, in the order a call hands them
     */
    public static CasesOfAnAnswer answerOf(AnalysisBody analysis, List<String> parameters,
                                           InputReading read, InputReads reads) {
        return Pullback.answerOf(analysis.core(), parameters, reads, read);
    }

    private InputReading read() {
        if (read == null) {
            read = reading.get();
        }
        return read;
    }

    private void walk(Core e, InputReads reads) {
        // A closure applied to each of the values a container was written with is read once per
        // application, each handing its parameter one of them, and what a site in it states is
        // what it states on the application a run meets it on.
        if (Core.withoutStanding(e) instanceof Core.Block block && !pastTheFigure) {
            switch (Pullback.applicationsOf(block, reads, symbols, newtypes)) {
                case InputReads.Applications.Each(var applications, var _) -> {
                    List<MeaningsOfABody> each = new ArrayList<>();
                    for (InputReads application : applications) {
                        MeaningsOfABodyReading inside = inside(false);
                        inside.walk(block.body(), application);
                        read = inside.read;
                        each.add(inside.filed.filed());
                    }
                    filed.metOnEachApplication(each);
                    return;
                }
                // More applications than are read: every condition in the body is filed as one
                // this compiler declined to read, and none is read on fewer of them than it is on.
                case InputReads.Applications.MoreThanAreRead _ -> {
                    MeaningsOfABodyReading inside = inside(true);
                    inside.walk(block.body(), reads);
                    read = inside.read;
                    inside.filed.filed().stated().forEach(filed::met);
                    return;
                }
                case InputReads.Applications.NoneHanded _, InputReads.Applications.Unsaid _ -> { }
            }
        }
        switch (Core.withoutStanding(e)) {
            case Core.If iff -> asked(iff.place().occurrence(),
                    MeaningsOfABody.Part.Asked.CONDITION, iff.cond(), reads);
            case Core.Binary binary when ConditionJoin.of(binary.op()).isPresent() ->
                    asked(binary.occurrence(), MeaningsOfABody.Part.Asked.LEFT, binary.left(),
                            reads);
            case Core.Binary binary when Comparison.of(binary).isPresent() ->
                    asked(binary.occurrence(), MeaningsOfABody.Part.Asked.ITSELF, binary, reads);
            case Core.Match match -> entered(match, match.place().occurrence(),
                    match.cases().size(), reads);
            case Core.IfConstructed attempt -> entered(attempt, attempt.occurrence(),
                    1 + attempt.els().size(), reads);
            default -> { }
        }
        ScopeStep.forEachChild(e, (child, step) -> walk(child,
                reads.entering(step, symbols, newtypes)));
    }

    /** A reading of a closure's body, sharing the reading of the input this one has made. */
    private MeaningsOfABodyReading inside(boolean pastTheFigure) {
        MeaningsOfABodyReading inside = new MeaningsOfABodyReading(reading, symbols, newtypes);
        inside.read = read;
        inside.pastTheFigure = pastTheFigure;
        return inside;
    }

    /** What {@code truth} states, filed at {@code part} of the construct {@code at} is one of. */
    private void asked(ConstructOccurrence at, MeaningsOfABody.Part.Asked part, Core truth,
                       InputReads reads) {
        Optional<ModelOccurrence> construct = ModelOccurrence.statedAt(at);
        if (construct.isEmpty()) {
            return;
        }
        filed.met(new MeaningsOfABody.Site(construct.get(), part), pastTheFigure
                ? declined(construct)
                : Pullback.ofATruth(truth, reads, read(), construct).meaning());
    }

    /**
     * What a run entering each of {@code fork}'s {@code arms} arms states, each filed at that arm
     * of the construct {@code at} is one of.
     */
    private void entered(Core fork, ConstructOccurrence at, int arms, InputReads reads) {
        Optional<ModelOccurrence> construct = ModelOccurrence.statedAt(at);
        if (construct.isEmpty()) {
            return;
        }
        // Every arm read off one reading of the fork, since what one states is the whole fork's.
        List<MeaningsOfABody.Meaning> entered = pastTheFigure
                ? Collections.nCopies(arms, declined(construct))
                : Pullback.ofTheArms(fork, reads, read(), construct).stream()
                        .map(Pullback.Pulled::meaning).toList();
        for (int part = 0; part < arms; part++) {
            filed.met(new MeaningsOfABody.Site(construct.get(), armOf(fork, part)),
                    entered.get(part));
        }
    }

    /** What a site inside a closure applied more times than a condition is read on states. */
    private static MeaningsOfABody.Meaning declined(Optional<ModelOccurrence> construct) {
        return new Conclusion(construct).meaningOf(new Derivation.Stopped(
                new WhyUnread.MoreReadingsThanAreMade(), false));
    }

    /**
     * Which arm of {@code fork} its arm {@code part} is, as {@link Choice} numbers them, named as a
     * site names it ({@link MeaningsOfABody.Part.Arm}): a case of a {@code match} by where it is
     * written, and an arm of an attempt by the clause it answers.
     *
     * @throws IllegalArgumentException where {@code fork} is no {@code match} or attempt with such
     *                                  an arm
     */
    public static MeaningsOfABody.Part.Arm armOf(Core fork, int part) {
        return switch (Core.withoutStanding(fork)) {
            case Core.Match match when part >= 0 && part < match.cases().size() ->
                    new MeaningsOfABody.Part.OfACase(part);
            case Core.IfConstructed _ when part == 0 -> new MeaningsOfABody.Part.Built();
            case Core.IfConstructed attempt when part > 0 && part <= attempt.els().size() ->
                    new MeaningsOfABody.Part.Departed(
                            attempt.els().get(part - 1).clause().map(ClauseName::new));
            default -> throw new IllegalArgumentException("arm " + part + " of "
                    + fork.getClass().getSimpleName() + " at " + fork.pos()
                    + " is no arm of a match or an attempt");
        };
    }
}
