package souther.bench;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Every figure this compiler stops a search at is read where a rule says it is read, and nowhere
 * else.
 *
 * <p>What a budget is for is being carried: a search that stopped at one says which, and an account
 * that reads it knows the point is open for a reason somebody could raise rather than because the
 * model refuses a row. That only works while every place a figure is reached is a place that hands
 * it over — a walk that consults one and comes back with a word alone is a stop that vanished, and
 * the word it comes back with is written wherever a walk stops for any reason at all, so nothing
 * downstream can tell that it happened.
 *
 * <p><b>So the places are counted rather than trusted.</b> Twice while this was written the list of
 * budgets was taken from the constants that looked like budgets, and twice it was short — once by a
 * figure spelled differently and once by a figure that is the size of a walk rather than a number
 * anybody wrote down. A name is not what makes a budget; being reached and stopping something is.
 *
 * <p>Each entry below says what that place does with the figure. A place added is a question, and
 * it has three answers rather than two: the place hands the budget over, or what it hands over is
 * carried somewhere else, or reaching the figure omits no work at all and there is nothing to carry.
 * The answer belongs beside the code that decides, which is why the list is here and not a count.
 *
 * <p><b>The third is an answer and not an excuse.</b> A figure whose channel is simply missing and
 * one that gives nothing up look alike from here — both are read and neither travels — and the
 * difference is the whole of whether a reader is owed something. So a place claiming it has to say
 * why nothing is lost, and the sentence has to be one somebody could find wrong.
 *
 * <p><b>One of two sheets.</b> A figure a class copies into a field of its own is reached once,
 * where the field is set, and the walk that then stops at the field is not a reader of the figure
 * here — so this holds the registered figures to being handed over, and
 * {@link EveryFigureTheComposingStageStopsAtIsABudgetOrIsSaidNotToBeTest} holds the classes to
 * registering a figure at all. Neither is enough alone: that one sees a number written down and
 * this one sees a figure that is the size of a walk.
 *
 * <p><b>And what neither sees is the predicate.</b> Each entry below says the place hands the
 * figure over; that the place reaches it only where there was more to do is not something either
 * sheet can read. What says that is the threshold tests, one either side of a figure and on it, and
 * they exist for the walks that can be put there.
 *
 * <p>Which is why a place that reaches a figure and a place that decides a walk was stopped are
 * worth keeping apart. A consumer here says it has no room for the piece in front of it and says
 * under which figure; that the walk was holding a piece at all is the walk's, and a walk that
 * records a figure without one is the reading these sheets cannot see going wrong.
 */
class EveryBudgetOfThisCompilerIsReadWhereItIsDeclaredToBeTest {

    private static final String BUDGET = "souther.compiler.partition.CompositionBudget";

    /**
     * Where a figure is read, and what that place does with it.
     *
     * <p>By the method and not by the class. A helper beside one that reads a figure answers for
     * nothing, and counting per class would let a second reader hide behind the first.
     */
    private static final Map<String, String> READ_AT = new LinkedHashMap<>(Map.ofEntries(
            // The figures themselves. Every other place asks one of these for its number.
            Map.entry("souther.compiler.partition.CompositionBudget#<clinit>()V",
                    "the figures, which is where they are"),

            // The stops. Each reaches a figure and hands it over as itself.
            Map.entry("souther.compiler.partition.Witnesses#<clinit>()V",
                    "how many pairings a map is built from at once"),
            // Every value built at a count asks these, and they say which figure it is past.
            Map.entry("souther.compiler.partition.Witnesses#pastTheElements(I)"
                            + "Lsouther/compiler/partition/CompositionBudget;",
                    "stops at the elements a value is built with, and says which"),
            Map.entry("souther.compiler.partition.Witnesses#pastTheCharacters(I)"
                            + "Lsouther/compiler/partition/CompositionBudget;",
                    "stops at the characters a string is built with, and says which"),
            Map.entry("souther.compiler.partition.Witnesses#ofMapping("
                            + "Lsouther/compiler/check/Shape$Mapping;I"
                            + "Lsouther/compiler/check/RuleReadingContext;Ljava/util/Set;)"
                            + "Lsouther/compiler/partition/Witnesses$Built;",
                    "stops at the pairings a map is built from at once, and says which"),
            // A total's two, one consumer each. The figure is asked for twice per consumer and for
            // two questions: whether there is room for the piece in front of it, and — where the
            // walk finds there was not — which figure to say so under. Held apart, a consumer could
            // report having run out of one figure while making room by another.
            //
            // Two and not three, because the ways a difference is spread are not held to a figure.
            // What is written of them is that this compiler writes some of them, which is no number
            // to raise and travels as a CompositionRepertoire rather than from here.
            Map.entry("souther.compiler.partition.ContainersAddingUp$HowManyElements#take("
                            + "Ljava/lang/Integer;)Lsouther/compiler/partition/Taking$Taken;",
                    "has no room for a count of more elements than a row carries"),
            Map.entry("souther.compiler.partition.ContainersAddingUp$HowManyElements#figure()"
                            + "Lsouther/compiler/partition/CompositionBudget;",
                    "says which figure that was, which is what the walk hands over"),
            // The same two for a total spread over the leaves of containers inside containers, where
            // the count is the leaves and not the elements of one.
            Map.entry("souther.compiler.partition.NestedContainersAddingUp$Walk#take("
                            + "Ljava/lang/Integer;)Lsouther/compiler/partition/Taking$Taken;",
                    "has no room for a count of more leaves than a row carries"),
            Map.entry("souther.compiler.partition.NestedContainersAddingUp$Walk#figure()"
                            + "Lsouther/compiler/partition/CompositionBudget;",
                    "says which figure that was, which is what the walk hands over"),
            Map.entry("souther.compiler.partition.ContainersAddingUp$WhatIsOffered#take("
                            + "Lsouther/compiler/partition/FixtureTemplate;)"
                            + "Lsouther/compiler/partition/Taking$Taken;",
                    "has no room for a container past as many as are offered"),
            Map.entry("souther.compiler.partition.ContainersAddingUp$WhatIsOffered#figure()"
                            + "Lsouther/compiler/partition/CompositionBudget;",
                    "says which figure that was, which is what the walk hands over"),
            Map.entry("souther.compiler.partition.ContainersAddingUp$Asking#next()"
                            + "Lsouther/compiler/partition/ConstructionPlan$Result;",
                    "stops asking about ways down to the number, which is the one place they are"
                            + " asked about, and hands the figure over with whatever the planning"
                            + " gave up at"),
            Map.entry("souther.compiler.partition.ContainersAddingUp$Asking#another()Z",
                    "stops building an element along a way with another choice of the values"
                            + " asked inside it, under the figure the ways down are counted by,"
                            + " and hands it over the same way"),
            // A count's two: the sizes a container is tried at and the containers offered for one
            // count, each said under its own figure in what the composing comes back with.
            Map.entry("souther.compiler.partition.CardinalityComposer#<clinit>()V",
                    "how many elements a container composed for a count holds, how many"
                            + " containers are offered for one, and how many ways of sharing its"
                            + " elements out are looked at"),
            // The values an element of a container is listed at, for the composer and for the most
            // a count of the elements comes to alike.
            Map.entry("souther.compiler.partition.ElementValues#<clinit>()V",
                    "how many values of an element are listed; the composer says the figure in"
                            + " what it comes back with, and a count whose values it stopped"
                            + " keeps the most its container holds, so the points between that"
                            + " and the values meeting its statement are searched and the search"
                            + " stops at this figure"),
            Map.entry("souther.compiler.partition.ACountHandedOn#<clinit>()V",
                    "how far a count handed on is looked for, which the composer says as that"
                            + " figure where none was found below it"),
            Map.entry("souther.compiler.partition.CardinalityComposer#compose("
                            + "Lsouther/compiler/types/Type;Ljava/util/List;Ljava/util/List;"
                            + "Ljava/util/List;Ljava/util/SequencedMap;"
                            + "Lsouther/compiler/partition/RealizationTarget$OfANumber;"
                            + "Ljava/util/List;Lsouther/compiler/inputs/Quantities;"
                            + "Lsouther/compiler/inputs/SearchRegion;"
                            + "Lsouther/compiler/check/RuleReadingContext;)"
                            + "Lsouther/compiler/partition/TermRealizations$Realization;",
                    "stops at a size or at the containers offered, and hands the figure over in"
                            + " the shortfall it comes back with"),
            Map.entry("souther.compiler.partition.CardinalityComposer#amongItsValues("
                            + "Ljava/util/List;Ljava/util/List;Ljava/util/List;"
                            + "Ljava/util/SequencedMap;Lsouther/compiler/inputs/TermPath;"
                            + "Lsouther/compiler/partition/NumericSet;"
                            + "Lsouther/compiler/types/Type;Lsouther/compiler/check/TypeView;"
                            + "Lsouther/compiler/check/Shape$Sequence;Ljava/util/List;"
                            + "Lsouther/compiler/inputs/Quantities;"
                            + "Lsouther/compiler/inputs/SearchRegion;"
                            + "Lsouther/compiler/check/RuleReadingContext;)"
                            + "Lsouther/compiler/partition/TermRealizations$Realization;",
                    "stops at the values an element is chosen among, at a size, at the sharings"
                            + " looked at or at the containers offered, and hands the figure over"
                            + " in the shortfall it comes back with"),
            // The ways a way is looked along where conditions on it came out one of several
            // things: the walk stops at either figure and says which, and each caller carries it
            // on with what was looked along.
            Map.entry("souther.compiler.partition.OneOfEach#walk("
                            + "Ljava/util/List;Lsouther/compiler/partition/OneOfEach$Vocabulary;"
                            + "Lsouther/compiler/partition/CompositionBudget;"
                            + "Lsouther/compiler/partition/CompositionBudget;)"
                            + "Lsouther/compiler/partition/OneOfEach$Walked;",
                    "stops at the choices looked at or at the ways looked along, and says which"
                            + " in what it comes back with"),
            Map.entry("souther.compiler.partition.OneOfEach$Group#from("
                            + "Ljava/util/Deque;Ljava/util/Map;Ljava/lang/Object;)Z",
                    "stops a group's walk at the choices looked at or at the ways handed on, and"
                            + " records which, which the walk says in what it comes back with"),
            Map.entry("souther.compiler.partition.WayToTheBorder#along()"
                            + "Lsouther/compiler/partition/OneOfEach$Walked;",
                    "hands both figures to the walk, whose answer says which it stopped at"),
            Map.entry("souther.compiler.partition.WayToTheBorder#takenByNoInput("
                            + "Lsouther/compiler/inputs/SearchRegion;"
                            + "Ljava/util/function/BooleanSupplier;)Ljava/util/Optional;",
                    "hands both figures to the walk, and a walk stopped at either is no proof:"
                            + " the way is kept"),
            Map.entry("souther.compiler.partition.ElementsWrittenAlike#of("
                            + "Lsouther/compiler/partition/Reachability$Reaching;)"
                            + "Lsouther/compiler/partition/ElementsWrittenAlike$Choices;",
                    "says the figure the walk stopped at beside the ways it looked along, which"
                            + " the way composed as it stands says of what it wrote alike"),
            Map.entry("souther.compiler.partition.CardinalityComposer#handingOn("
                            + "Ljava/util/List;Ljava/util/List;Ljava/util/List;"
                            + "Lsouther/compiler/partition/NumericSet;"
                            + "Lsouther/compiler/check/TypeView;Ljava/util/List;"
                            + "Lsouther/compiler/check/RuleReadingContext;)"
                            + "Lsouther/compiler/partition/TermRealizations$Realization;",
                    "stops at a size or at the containers offered, and hands the figure over in"
                            + " the shortfall it comes back with"),
            Map.entry("souther.compiler.partition.CardinalityComposer#composeAlike("
                            + "Lsouther/compiler/types/Type;Ljava/util/List;"
                            + "Lsouther/compiler/partition/RealizationTarget$OfANumber;"
                            + "Lsouther/compiler/partition/RealizationTarget$OfANumber;"
                            + "Ljava/util/SequencedMap;Lsouther/compiler/inputs/Quantities;"
                            + "Lsouther/compiler/inputs/SearchRegion;"
                            + "Lsouther/compiler/check/RuleReadingContext;)"
                            + "Lsouther/compiler/partition/TermRealizations$Realization;",
                    "stops at the containers offered and at the most elements a container is"
                            + " composed with, and hands the figure over in the shortfall it"
                            + " comes back with"),
            Map.entry("souther.compiler.partition.LevelRealizer#ofACount("
                            + "Lsouther/compiler/partition/Standing$OfACount;"
                            + "Lsouther/compiler/inputs/SearchRegion;"
                            + "Lsouther/compiler/partition/WitnessSearch;"
                            + "Lsouther/compiler/partition/ValuesTried;)"
                            + "Lsouther/compiler/partition/Realization;",
                    "says the counts were offered short where the source of them stopped, as a"
                            + " side's levels are"),
            Map.entry("souther.compiler.partition.LevelRealizer#ofACountAndAForm("
                            + "Lsouther/compiler/partition/Standing$OfACountAndAForm;"
                            + "Lsouther/compiler/inputs/SearchRegion;"
                            + "Ljava/util/Map;"
                            + "Lsouther/compiler/partition/WitnessSearch;"
                            + "Lsouther/compiler/partition/ValuesTried;)"
                            + "Lsouther/compiler/partition/Realization;",
                    "tries the counts from none up to as many as a container is composed with, and"
                            + " says that figure where it came to the end of them without a row"),
            Map.entry("souther.compiler.partition.Generator#inputsFrom("
                            + "Lsouther/compiler/partition/Generator$RowBeingComposed;I"
                            + "[Lsouther/compiler/partition/FixtureTemplate;"
                            + "Lsouther/compiler/partition/ValuesHandedOn;)"
                            + "Lsouther/compiler/partition/Generator$RowComposed;",
                    "says a baseline whose every written way was refused was written fewer ways"
                            + " than it had, under the figure the ways were cut at"),
            // The runs looking for a row that goes further than one already found: one counter
            // holds the figure, and the exchange says it beside the row for each way whose search
            // was refused a run. The row found goes out whatever this comes to.
            Map.entry("souther.compiler.partition.Generator$GoingOn$Runs#<init>()V",
                    "the runs one row's exchange may make, which is where the count starts"),
            Map.entry("souther.compiler.partition.Generator$GoingOn#past("
                            + "Lsouther/compiler/partition/MeasuredInput$MeasuredAxes;"
                            + "Lsouther/compiler/partition/Generator$Pins;Ljava/util/List;"
                            + "Lsouther/compiler/partition/Generator$Searched;"
                            + "Lsouther/compiler/partition/Generator$CandidateCheck;"
                            + "Lsouther/compiler/partition/FixtureReferences;Ljava/util/List;)"
                            + "Lsouther/compiler/partition/Generator$Composed;",
                    "says a way past a guard whose search was refused a run was cut short under the"
                            + " figure, beside the row that goes out"),
            // The ways under the cases of a sum a container, or a requirement at a name the cases
            // share, is written: one walk hands them over, and says the figure where it stopped,
            // which both roads a row is composed on carry with what the ways tried came to — rows
            // passed over included.
            Map.entry("souther.compiler.partition.ContentsAsked$UnderTheCases#tryEach("
                            + "Ljava/util/function/Predicate;)"
                            + "Lsouther/compiler/partition/ContentsAsked$UnderTheCases$Walked;",
                    "stops handing over ways under the cases with some left, and answers that it"
                            + " stopped at the figure rather than that every way was tried"),
            Map.entry("souther.compiler.partition.ContentsAsked$UnderTheCases#foundOut("
                            + "Lsouther/compiler/partition/ContentsAsked$UnderTheCases$Walked;)"
                            + "Lsouther/compiler/partition/SearchShortfall;",
                    "hands the figure over in what the walk found out about the ways it did not"
                            + " try, where it stopped there"),
            Map.entry("souther.compiler.partition.LevelRealizer#<clinit>()V",
                    "the places a pair is tried at and the places of its line looked at to find"
                            + " them, the steps, the progression — and the re-reads,"
                            + " which travel nowhere because reaching that one gives nothing up:"
                            + " the walk carries on against the wider box, which offers every"
                            + " assignment the narrowing would have and skips none of them"),
            Map.entry("souther.compiler.partition.LevelRealizer#ofTwo("
                            + "Lsouther/compiler/partition/Standing$OfTwoOnOneCarrier;"
                            + "Lsouther/compiler/inputs/SearchRegion;"
                            + "Ljava/util/Map;"
                            + "Lsouther/compiler/partition/WitnessSearch;"
                            + "Lsouther/compiler/partition/ValuesTried;)"
                            + "Lsouther/compiler/partition/Realization;",
                    "stops walking a line at the places it tries and says which figure"),
            Map.entry("souther.compiler.query.Coverages$2#lookedAlong("
                            + "Lsouther/compiler/partition/Criterion;Ljava/lang/String;"
                            + "Ljava/util/function/UnaryOperator;"
                            + "Lsouther/compiler/partition/Reachability$Reaching;)"
                            + "Lsouther/compiler/query/Coverages$2$Looked;",
                    "stops asking a point for another value to stand a row on, along the whole way"
                            + " or one of the ways it is, and answers with what the values it did"
                            + " try came to"),
            // The pairs of a number of the input and the answer composed for it. The figure bounds
            // how many are offered, and what it hands over is whether some were left out, which the
            // search that composed for none of them answers with.
            // The ways a statement about an answer is looked along where it asks one of several
            // things. Past the figure they are not split, and what asked for them is said to be a
            // demand no value was composed against.
            Map.entry("souther.compiler.partition.AnAnswerComposed#of("
                            + "Lsouther/compiler/partition/MeasuredInput;"
                            + "Lsouther/compiler/partition/StatementsOfAnInput;"
                            + "Ljava/util/Map;Ljava/util/List;)"
                            + "Lsouther/compiler/partition/AnAnswerComposed$Attempt;",
                    "past the figure does not look along the ways of a statement, and says that"
                            + " nothing was composed against it"),
            Map.entry("souther.compiler.partition.InputNumbersAnAnswerTurnsOn#solvedAtTheEnds("
                            + "Lsouther/compiler/numeric/ExactRatio;"
                            + "Lsouther/compiler/numeric/ExactRatio;"
                            + "Ljava/util/List;Ljava/util/List;"
                            + "Lsouther/compiler/inputs/SearchRegion;Ljava/util/Set;)"
                            + "Ljava/util/List;",
                    "stops the walk over the ends of an answer's places at the figure, says so to"
                            + " the caller, and offers what it had solved for — values to put a"
                            + " number at, which the pairs' own figure then bounds again"),
            Map.entry("souther.compiler.partition.InputNumbersAnAnswerTurnsOn#of("
                            + "Lsouther/compiler/partition/AnswersDemanded;"
                            + "Lsouther/compiler/partition/Reachability$Reaching;"
                            + "Lsouther/compiler/partition/InputNumbersAnAnswerTurnsOn$AnswerSubjectOf;"
                            + "Lsouther/compiler/partition/StatementsOfAnInput;)"
                            + "Lsouther/compiler/partition/InputNumbersAnAnswerTurnsOn$Pairs;",
                    "stops offering pairs at the figure and says whether some were left out"),
            Map.entry("souther.compiler.query.Coverages$2#endedBy("
                            + "Lsouther/compiler/query/SearchOutcomes;"
                            + "Lsouther/compiler/partition/Realization;)"
                            + "Lsouther/compiler/query/SearchOutcomes;",
                    "hands that figure on with the answer where the realizer had a value left to"
                            + " give, which is what says the answer is about fewer values than the"
                            + " point had"),
            Map.entry("souther.compiler.partition.LevelRealizer#ofAForm("
                            + "Lsouther/compiler/partition/Standing$OfAForm;"
                            + "Lsouther/compiler/inputs/SearchRegion;"
                            + "Ljava/util/Map;"
                            + "Lsouther/compiler/partition/ValuesTried;)"
                            + "Lsouther/compiler/partition/Realization;",
                    "collects what the level walks ran out of, and the levels it was offered"),
            Map.entry("souther.compiler.partition.LevelRealizer#ofOne("
                            + "Lsouther/compiler/partition/Standing$OfOneCoordinate;"
                            + "Lsouther/compiler/inputs/SearchRegion;"
                            + "Ljava/util/Map;"
                            + "Lsouther/compiler/partition/WitnessSearch;"
                            + "Lsouther/compiler/partition/ValuesTried;)"
                            + "Lsouther/compiler/partition/Realization;",
                    "counts the places a point was offered and hands the figure on with the answer"
                            + " where it offered as many as it may"),
            Map.entry("souther.compiler.partition.LevelRealizer#someMemberIn("
                            + "Lsouther/compiler/partition/Criterion$Within;"
                            + "Ljava/util/List;"
                            + "Lsouther/compiler/check/Carrier;"
                            + "Lsouther/compiler/values/ValueSet;"
                            + "Lsouther/compiler/numeric/Congruences;"
                            + "Lsouther/compiler/numeric/PlacesApart;"
                            + "Ljava/util/Set;)"
                            + "Lsouther/compiler/numeric/Place;",
                    "puts the figure beside the answer where a run held more members of the class"
                            + " than were looked at"),
            Map.entry("souther.compiler.partition.TermRealizations#membersOnTheOrder("
                            + "Lsouther/compiler/partition/NumericSet;"
                            + "Lsouther/compiler/inputs/TermOrders;"
                            + "Lsouther/compiler/numeric/Congruences;"
                            + "Lsouther/compiler/numeric/NumericDomain$Bounds;"
                            + "Ljava/util/Set;)"
                            + "Lsouther/compiler/partition/TermRealizations$Tried;",
                    "says in what it hands back that a run held more members than it offered, by"
                            + " the figure it was cut at"),
            Map.entry("souther.compiler.partition.LevelRealizer#ofARemainder("
                            + "Lsouther/compiler/partition/Standing$OfARemainder;"
                            + "Lsouther/compiler/inputs/SearchRegion;"
                            + "Ljava/util/Map;"
                            + "Lsouther/compiler/partition/ValuesTried;)"
                            + "Lsouther/compiler/partition/Realization;",
                    "collects what the level walks ran out of, the levels it was offered and the"
                            + " members of a class it left untried"),
            Map.entry("souther.compiler.partition.LevelRealizer$Search#stepsLeft()Z",
                    "the steps a search may take, marked where there is no room for another"),
            Map.entry("souther.compiler.partition.LevelRealizer$Search#outward("
                            + "ILsouther/compiler/partition/CandidateDomain$Outward;"
                            + "Lsouther/compiler/numeric/ExactRatio;"
                            + "Lsouther/compiler/numeric/ExactRatio;"
                            + "Lsouther/compiler/inputs/SearchRegion;)"
                            + "Lsouther/compiler/partition/LevelRealizer$Reached;",
                    "walks a progression as far as this walks one, and says that is why"),
            Map.entry("souther.compiler.partition.LevelCandidateSource#<clinit>()V",
                    "how many levels a side is asked at"),
            Map.entry("souther.compiler.partition.NumericWitness#<clinit>()V",
                    "how many values a position on the way is tried at, and how many places of its"
                            + " run are looked at to find them"),
            Map.entry("souther.compiler.partition.NumericWitness#walk("
                            + "Lsouther/compiler/inputs/SearchRegion;Ljava/util/List;I"
                            + "Ljava/util/function/Function;"
                            + "Lsouther/compiler/partition/WitnessSearch;"
                            + "Lsouther/compiler/partition/NumericWitness$Composing;"
                            + "Ljava/util/SequencedMap;"
                            + "Lsouther/compiler/partition/NumericWitness$Met;)Z",
                    "stops trying values of a position on the way and says which figure"),
            Map.entry("souther.compiler.partition.Generator$WayComposer#composes("
                            + "Ljava/util/Map;Ljava/util/Set;Ljava/util/Map;"
                            + "Ljava/util/SequencedMap;Ljava/util/SequencedMap;Ljava/util/List;)"
                            + "Lsouther/compiler/partition/NumericWitness$Composed;",
                    "stops composing for the values of the numbers on the way and says which"
                            + " figure"),
            Map.entry("souther.compiler.partition.Generator#<clinit>()V",
                    "how many assignments a search composes"),
            Map.entry("souther.compiler.partition.Generator#conditioned("
                            + "Lsouther/compiler/partition/ConstructionPlan;Ljava/util/Map;"
                            + "Ljava/util/Map;"
                            + "Lsouther/compiler/partition/Generator$Composing;"
                            + "Lsouther/compiler/partition/ConditionedCandidates;)"
                            + "Lsouther/compiler/partition/Generator$Outcome;",
                    "the assignments a descent composes, marked where the bound is reached"),
            Map.entry("souther.compiler.partition.Generator#over("
                            + "Ljava/util/List;Ljava/util/List;"
                            + "Lsouther/compiler/partition/Generator$Composing;"
                            + "Lsouther/compiler/partition/Generator$ValueTaking;)"
                            + "Lsouther/compiler/partition/Generator$Outcome;",
                    "the same bound over one pass of the assignments"),
            Map.entry("souther.compiler.partition.ConstructionPlan#node("
                            + "Lsouther/compiler/types/Type;"
                            + "Lsouther/compiler/inputs/TermPath;"
                            + "Lsouther/compiler/check/NewtypeInners;"
                            + "Lsouther/compiler/check/Symbols;"
                            + "Lsouther/compiler/check/DeclarationKinds;"
                            + "Lsouther/compiler/check/SumCases;I"
                            + "Ljava/util/Set;"
                            + "Lsouther/compiler/inputs/Requirements;"
                            + "Lsouther/compiler/partition/ConstructionPlan$ContentsComposed;"
                            + "Lsouther/compiler/partition/ConstructionPlan$WhatItMayHold;)"
                            + "Lsouther/compiler/partition/ConstructionPlan$NodeResult;",
                    "stops descending where a value is still made of positions, and says which"
                            + " figure — on the position where it stopped, or as the whole plan"
                            + " where the caller asked for something below it"),

            // The reading of what a body decides. The figure is what the reading of the ways will
            // hold apart, and where it will not, the rules are none of the body's rather than some
            // of them -- so what is carried out is the figure itself.
            Map.entry("souther.compiler.partition.Pullback#<clinit>()V",
                    "how many readings of one condition the reading of what it means makes"),
            Map.entry("souther.compiler.partition.DemandReading#<clinit>()V",
                    "how many ways an element may meet what a quantifier asks are read one by one"),
            Map.entry("souther.compiler.partition.DemandReading$AnElementsWay#walk("
                            + "Ljava/util/List;I"
                            + "Lsouther/compiler/partition/DemandReading$AnElementsWay;"
                            + "Lsouther/compiler/inputs/SearchRegion;Ljava/util/Set;[I)Z",
                    "past the figure stops making ways whole, keeps the ones made and says the"
                            + " rest are where this compiler's work stopped"),
            Map.entry("souther.compiler.partition.DemandReading$AnElementsWay#oneOfEach("
                            + "Ljava/util/List;)Ljava/util/List;",
                    "past the figure stops taking the ways of one of several things, keeps the"
                            + " ones taken and says the rest stopped, the same way"),
            Map.entry("souther.compiler.partition.Pullback#applicationsOf("
                            + "Lsouther/compiler/core/Core$Block;"
                            + "Lsouther/compiler/inputs/InputReads;"
                            + "Lsouther/compiler/inputs/InputReading;)"
                            + "Lsouther/compiler/inputs/InputReads$Applications;",
                    "hands the figure to the counting of a closure's applications, which answers"
                            + " that there are more than are read; every reader of that answer"
                            + " carries it out as a part nothing read, naming the figure"),
            Map.entry("souther.compiler.partition.Pullback#ofAChoice("
                            + "Lsouther/compiler/check/StatedComparison;"
                            + "Lsouther/compiler/inputs/Denotation;"
                            + "Lsouther/compiler/inputs/InputReads;)"
                            + "Lsouther/compiler/meaning/Derivation;",
                    "counts the cases a comparison is split into, and past the figure carries"
                            + " the comparison out as a part nothing read, naming it"),
            Map.entry("souther.compiler.partition.Pullback#answered("
                            + "Lsouther/compiler/inputs/Denotation;"
                            + "Lsouther/compiler/meaning/WhyUnread$AtNoPosition$Place;)"
                            + "Lsouther/compiler/meaning/WhichCase;",
                    "counts the arms a value chosen by cases is read through — a body's answer, or"
                            + " what a match chooses by — and past the figure carries which case it"
                            + " is out as unread, naming it"),
            // The readings every split makes, one way down and in all. Each place that splits — a
            // value gone into, a comparison of a choice, a law read of each value or application,
            // a sum over values written out — asks here before reading any of them, and past
            // either figure carries what it would have read out as a part nothing read, naming
            // the one it reached.
            Map.entry("souther.compiler.partition.Pullback#splitInto("
                            + "Lsouther/compiler/inputs/InputReads;J)"
                            + "Lsouther/compiler/meaning/WhyUnread;",
                    "counts the readings a split makes along one way down, and says which figure"
                            + " where they are past it"),
            Map.entry("souther.compiler.partition.Pullback#<init>("
                            + "Lsouther/compiler/inputs/InputReading;Ljava/util/Optional;)V",
                    "how many readings one reading of a condition makes in all, which every split"
                            + " takes its readings from and past which it says which figure"),
            // What a step of a reading concludes, written out. Past the figure the step is
            // concluded as a part nothing read, naming it.
            Map.entry("souther.compiler.meaning.Conclusion#<clinit>()V",
                    "how many parts a step of a reading is concluded with"),
            Map.entry("souther.compiler.meaning.Conclusion#of("
                            + "Lsouther/compiler/meaning/Derivation;)"
                            + "Lsouther/compiler/meaning/Proposition;",
                    "past the figure concludes the step as a part nothing read, naming it"),
            Map.entry("souther.compiler.meaning.Conclusion#partsIn("
                            + "Lsouther/compiler/meaning/Proposition;)J",
                    "counts the parts a statement comes to written out no further than one past"
                            + " the figure"),
            // Where one line of a statement of several decides: the statement read, its cases
            // taken apart, and each asked whether rows stand on both sides of the line. Past any
            // of the figures the line is one where it decides was not worked out, naming the
            // figure.
            Map.entry("souther.compiler.meaning.WhereEachLineDecides$Lifting#<init>()V",
                    "how many places quantifiers are said outside in, past which nothing of the"
                            + " statement is read and every line is said for cases nobody took"
                            + " apart"),
            Map.entry("souther.compiler.meaning.WhereEachLineDecides$Reading#<init>("
                            + "Lsouther/compiler/meaning/Proposition;Z)V",
                    "how many steps the statement is read in, past which its lines are said for"
                            + " cases nobody took apart"),
            Map.entry("souther.compiler.meaning.WhereEachLineDecides$Reading#takenApart("
                            + "Lsouther/compiler/meaning/Proposition;I)"
                            + "Lsouther/compiler/meaning/WhereEachLineDecides$TakenApart;",
                    "how many steps one line's cases are taken apart in, past which it says so"),
            Map.entry("souther.compiler.meaning.WhereEachLineDecides$Reading#turnsOn("
                            + "Lsouther/compiler/meaning/Proposition;)Ljava/util/List;",
                    "how many cases where a line decides are taken apart, past which the cases"
                            + " are kept as nobody taking them apart, naming the figure that"
                            + " stopped it"),
            Map.entry("souther.compiler.meaning.CasesOfALineAsked#<init>("
                            + "Ljava/util/function/Predicate;)V",
                    "how many times the cases one case was said for are asked, which every"
                            + " question spends"),
            Map.entry("souther.compiler.meaning.CasesOfALineAsked#asked("
                            + "Lsouther/compiler/meaning/DecidingCase;)"
                            + "Lsouther/compiler/meaning/CasesOfALineAsked$Found;",
                    "how many ways of choosing a case are asked, counted before any is: past the"
                            + " figure, more cases than are taken apart, and none is asked"),
            Map.entry("souther.compiler.meaning.CasesOfALineAsked#pastTheSteps("
                            + "Ljava/util/List;)V",
                    "out of steps, naming them and the cases left nobody took apart"),
            Map.entry("souther.compiler.partition.ComparisonAssessment#aPartNarrowed("
                            + "Lsouther/compiler/partition/ComparisonAssessment$Several$Part;"
                            + "Lsouther/compiler/partition/Reachability;"
                            + "Ljava/util/function/Function;"
                            + "Ljava/util/List;ZLsouther/compiler/inputs/InputReading;)"
                            + "Ljava/util/List;",
                    "hands the figure the asking stopped at to the line, as one where it decides"
                            + " in those cases was not worked out"),
            // What a path takes in of a condition: the parts of a disjunction taken alone, across
            // every disjunction inside another. Past the figure the disjunction is declined,
            // naming it.
            Map.entry("souther.compiler.check.MeaningAssumptions$Tries#<init>()V",
                    "how many parts of a disjunction one reading of a condition takes alone,"
                            + " past which the disjunction is declined for that figure"),
            Map.entry("souther.compiler.partition.Pullback$ALawRead#ofEachWrittenOut("
                            + "Lsouther/compiler/check/DeclaredArgument;"
                            + "Ljava/util/List;"
                            + "Lsouther/compiler/semantics/LawProposition;)"
                            + "Lsouther/compiler/partition/Pullback$WrittenOutRead;",
                    "counts the values a law is read of one by one, and past the figure carries"
                            + " the law out as a part nothing read, naming it"),
            Map.entry("souther.compiler.partition.Pullback#pastTheReadings("
                            + "Lsouther/compiler/meaning/Relation;)Z",
                    "counts the choices of which values written out meet a statement that a"
                            + " comparison of how many do admits against the figure, for the two"
                            + " places a comparison is made to carry it out as a part nothing"
                            + " read, naming it"),
            Map.entry("souther.compiler.partition.Pullback$ALawRead#compared("
                            + "Lsouther/compiler/semantics/LawProposition$Compared;)"
                            + "Lsouther/compiler/meaning/Derivation;",
                    "hands the figure to the comparison a law states, which writes a count of"
                            + " statements out as no more choices than it, and past the figure"
                            + " carries the comparison out as a part nothing read, naming it"),
            Map.entry("souther.compiler.partition.Pullback#onAnOrder("
                            + "Lsouther/compiler/check/StatedComparison;"
                            + "Lsouther/compiler/partition/AffineReading$OfAComparison;"
                            + "Lsouther/compiler/inputs/InputReads;)"
                            + "Lsouther/compiler/meaning/Derivation;",
                    "hands the figure to a comparison on an order, which holds no count of"
                            + " statements to write out"),
            Map.entry("souther.compiler.partition.Pullback#aRelation("
                            + "Lsouther/compiler/meaning/Derivation$ComparisonReading;"
                            + "Lsouther/compiler/numeric/LinearForm;"
                            + "Lsouther/compiler/numeric/Rel;"
                            + "Ljava/util/Map;"
                            + "Lsouther/compiler/meaning/Derivation$AComparisonRead$Facing;)"
                            + "Lsouther/compiler/meaning/Derivation;",
                    "counts the choices of which values written out meet a statement that a"
                            + " comparison of how many do admits, and past the figure carries the"
                            + " comparison out as a part nothing read, naming it"),
            Map.entry("souther.compiler.partition.DecisionReading#<clinit>()V",
                    "how many paths through one body a decision is read for"),
            Map.entry("souther.compiler.partition.WaysNoInputTakes#<init>()V",
                    "omits no work a reader is owed: a condition not taken in narrows nothing, a"
                            + " way not proved is a way kept, and the rules past it are read and"
                            + " said as rules, as with no proof at all"),
            Map.entry("souther.compiler.partition.DecisionReading#of("
                            + "Ljava/lang/String;Lsouther/compiler/check/AnalysisBody;"
                            + "Lsouther/compiler/inputs/InputReading;"
                            + "Lsouther/compiler/inputs/InputReads;)"
                            + "Lsouther/compiler/partition/DecisionReading;",
                    "hands the figure to the reading of the ways, and says which it reached"),

            // The numbers of a set an account walks. Each of these is an account whose numbers are
            // whole and whose window is wider than the figure, so the figure bounds how many it
            // tries and what it hands over beside them is whether it ran out of numbers first.
            Map.entry("souther.compiler.partition.TermRealizations#holding("
                            + "Lsouther/compiler/types/Type;Ljava/util/List;"
                            + "Lsouther/compiler/partition/AskedAt;"
                            + "Lsouther/compiler/inputs/TermOrders;"
                            + "Lsouther/compiler/check/RuleReadingContext;)"
                            + "Lsouther/compiler/partition/TermRealizations$Realization;",
                    "how many counts a container is asked to hold, and whether they were all the"
                            + " set admits"),
            Map.entry("souther.compiler.partition.TermRealizations#holdingThatManyOfAClass("
                            + "Lsouther/compiler/semantics/CodePointClass;"
                            + "Lsouther/compiler/types/Type;"
                            + "Lsouther/compiler/partition/AskedAt;"
                            + "Lsouther/compiler/inputs/TermOrders;"
                            + "Lsouther/compiler/check/RuleReadingContext;)"
                            + "Lsouther/compiler/partition/TermRealizations$Realization;",
                    "how many counts a string is asked to hold of a class, and whether they were"
                            + " all the set admits"),
            Map.entry("souther.compiler.partition.TermRealizations#lengthsFrom(I)"
                            + "Ljava/util/List;",
                    "how far past a count a string the type admits is looked for; a plain string"
                            + " is offered whichever is found, so reaching it gives up no count"),
            Map.entry("souther.compiler.partition.TermRealizations#stringsHoldingTheirCounts("
                            + "Ljava/util/Map;Lsouther/compiler/types/Type;"
                            + "Ljava/util/SequencedMap;"
                            + "Lsouther/compiler/inputs/SearchRegion;"
                            + "Lsouther/compiler/check/RuleReadingContext;)"
                            + "Lsouther/compiler/partition/TermRealizations$Realization;",
                    "how many numbers of each demand are tried, up to which count every way of"
                            + " writing a string is looked at, and how many steps the search may"
                            + " take: each is handed over as what stopped it where nothing was"
                            + " found"),
            Map.entry("souther.compiler.partition.TermRealizations#dateAnsweringMovedParts("
                            + "Ljava/util/List;Lsouther/compiler/check/Carrier;)"
                            + "Lsouther/compiler/partition/TermRealizations$Search;",
                    "how many years the first year asked is walked over, and whether they were all"
                            + " of them; with no year asked, one cycle of the calendar is walked,"
                            + " which is every day there is"),
            Map.entry("souther.compiler.partition.TermRealizations#wholeNumbers("
                            + "Lsouther/compiler/numeric/NumericDomain$Bounds;"
                            + "Ljava/util/function/Predicate;"
                            + "Ljava/math/BigInteger;Ljava/math/BigInteger;I)"
                            + "Lsouther/compiler/partition/TermRealizations$Tried;",
                    "names the figure as what left more of the set untried, where the walk filled"
                            + " what it was allowed before the window ran out"),
            // The number of a run that leaves the remainders asked for, solved for. A figure bounds
            // how many remainders of each demand and how many combinations of them are tried, and
            // what it hands over is the answer that says a figure stopped it.
            Map.entry("souther.compiler.partition.RemainderSolutions#solve("
                            + "Ljava/util/List;"
                            + "Lsouther/compiler/partition/RemainderSolutions$Value;"
                            + "Lsouther/compiler/check/Carrier;)"
                            + "Lsouther/compiler/partition/RemainderSolutions$Answer;",
                    "names the figure as what left remainders or combinations untried, as an"
                            + " answer apart from there being no number"),
            Map.entry("souther.compiler.partition.RemainderSolutions#choicesOf("
                            + "Lsouther/compiler/partition/RemainderSolutions$Demand;"
                            + "Ljava/math/BigInteger;Lsouther/compiler/check/Carrier;)"
                            + "Lsouther/compiler/partition/RemainderSolutions$Choices;",
                    "holds how many of a demand's remainders are tried, and says whether they were"
                            + " every one it admits, which is what the answer above says it stopped"
                            + " at"),
            // The numbers a place may be where several of its quotients are asked for. The run the
            // demands leave is walked as whole numbers, so the figure bounds how many of them are
            // tried — and what it hands over is that walk's own answer.
            Map.entry("souther.compiler.partition.TermRealizations#numbersInside("
                            + "Lsouther/compiler/numeric/NumericDomain$Bounds;"
                            + "Lsouther/compiler/check/Carrier;Ljava/util/function/Predicate;)"
                            + "Lsouther/compiler/partition/TermRealizations$Tried;",
                    "how many numbers of the run the demands leave are tried, and whether they"
                            + " were all of it"),
            Map.entry("souther.compiler.partition.TermRealizations#onMovedDates("
                            + "Ljava/util/List;Lsouther/compiler/types/Type;"
                            + "Lsouther/compiler/check/Carrier;"
                            + "Lsouther/compiler/check/RuleReadingSource;)"
                            + "Lsouther/compiler/partition/TermRealizations$Realization;",
                    "names the figure where no date was found and the years were not all walked"),

            // The readings. Each takes a figure that was handed over and says what it comes to.
            Map.entry("souther.compiler.partition.Generator$UnresolvedCombination$Reason#wordFor("
                            + "Ljava/util/Collection;)"
                            + "Lsouther/compiler/partition/Generator$UnresolvedCombination$Reason;",
                    "the word a search stopped by these comes back with"),
            Map.entry("souther.compiler.report.Reasons#said("
                            + "Lsouther/compiler/publish/CanonicalSelection;)Ljava/lang/String;",
                    "what a figure is called where a reader meets one"),
            // The order. It reaches every figure and hands none of them anywhere: what it decides
            // is which of them a reader is told about first, where two were reached.
            Map.entry("souther.compiler.publish.PublicationOrders#<clinit>()V",
                    "the order the figures are said in, where a search met more than one"),
            Map.entry("souther.compiler.query.EstablishmentGap$Composition#runSensitivity()"
                            + "Lsouther/compiler/observe/RunSensitivity;",
                    "asks each figure of a gap whether a wider run goes past it"),
            // A budget as the figure a reader is told stopped something: what it is called, what
            // it counts and what it stands at, read off the budget and handed on with it.
            Map.entry("souther.compiler.observe.Figure$Budget#name()Ljava/lang/String;",
                    "what a budget reached is called where a reader is told it stopped something"),
            Map.entry("souther.compiler.observe.Figure$Budget#counts()Ljava/lang/String;",
                    "what a budget reached counts, in a reader's words"),
            Map.entry("souther.compiler.observe.Figure$Budget#most()Ljava/lang/String;",
                    "the number a budget reached stands at"),
            Map.entry("souther.compiler.partition.Generator$ReplacementWitness#asFigures("
                            + "Ljava/util/Collection;)Ljava/util/List;",
                    "hands the budgets a search for a rewrite's row met on as the figures it"
                            + " stopped at"),
            Map.entry("souther.compiler.query.EstablishmentGap$Composition#figures()"
                            + "Ljava/util/List;",
                    "names the budgets a gap was stopped at, where they are all that held it open"),
            Map.entry("souther.compiler.query.Weakening#figures()Ljava/util/List;",
                    "names the budget a decision's reading stopped at, for a reader told a wider"
                            + " run may read past it"),
            // Which figure each reason a part was not read or a condition not taken in stopped at,
            // said once for every reader that names the figure: a gap on the way, a rule that
            // drew no line, a composer of an answer.
            Map.entry("souther.compiler.meaning.WhyUnread#figure()Ljava/util/Optional;",
                    "the figure each reason a part was not read stopped at, which every reader"
                            + " naming the figure reads"),
            Map.entry("souther.compiler.meaning.WhyNotTaken#figure()Ljava/util/Optional;",
                    "the figure each reason a condition was not taken in stopped at, the same"
                            + " way"),
            Map.entry("souther.compiler.report.AdequacyReport#whyDeclined("
                            + "Lsouther/compiler/meaning/WhyNotTaken;)Ljava/lang/String;",
                    "what the figure a path stopped taking a disjunction at counts, in the words"
                            + " a reader is told why a condition was not taken in")));

    /**
     * The places that read a figure are the places that say they do.
     *
     * <p>Both ways round. A place missing from the list is one nobody has said what it does with
     * the figure it reached; a place in the list that reads none is a rule about code that has gone.
     */
    @Test
    void aFigureIsReachedOnlyWhereSomethingSaysWhatItDoesWithIt() throws Exception {
        Set<String> found = new LinkedHashSet<>();
        for (Compiled.Site site : Compiled.sites()) {
            if (site.owner().equals(BUDGET) && !site.member().equals("<init>")
                    && !site.from().equals(BUDGET)
                    && !javacsOwn(site.from(), site.method())) {
                found.add(site.at());
            }
        }
        // The figures' own class reads itself, which is what an enum is; counted as a reader, every
        // constant would be a place to explain.
        found.add(BUDGET + "#<clinit>()V");

        List<String> unsaid = new ArrayList<>(found);
        unsaid.removeAll(READ_AT.keySet());
        List<String> gone = new ArrayList<>(READ_AT.keySet());
        gone.removeAll(found);

        assertEquals(List.of(), unsaid,
                "a figure of this compiler's reached where nothing says what it does with it."
                        + " Either it hands the budget over, and the list says so, or it swallows"
                        + " it — and a swallowed budget is a stop nothing downstream can see");
        assertEquals(List.of(), gone,
                "a rule about a place that no longer reads a figure");
    }

    /**
     * A class javac wrote, which is not a place anybody decided anything.
     *
     * <p>A switch over the figures compiles to a table beside the class that switches, and the
     * table reads every constant to number them. Counted as readers, every exhaustive switch would
     * be a place to write a sentence about — and the sentence would be about the switch, which is
     * already named here by the method that holds it.
     *
     * <p>The table is built where a class is prepared, which is what tells it from a class somebody
     * wrote. An anonymous class is named the same way and its methods are code as much as any
     * other's, so a figure read in one is a figure read here — exempted by the name alone, the one
     * place the reading of a border spends this compiler's figures was a place nothing asked about.
     */
    private static boolean javacsOwn(String from, String method) {
        int nested = from.lastIndexOf('$');
        return nested >= 0 && from.length() > nested + 1
                && Character.isDigit(from.charAt(nested + 1))
                && method.equals("<clinit>");
    }
}
