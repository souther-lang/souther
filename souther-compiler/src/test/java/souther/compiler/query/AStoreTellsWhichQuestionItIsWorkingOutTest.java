package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.ACompiledModel;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A store tells whoever listens which question it is working out ({@link Answering}), and
 * {@link WhatIsBeingMeasured} reads off that which behavior a compilation is on.
 *
 * <p>The calls nest as the questions do, which is what lets a listener keep the questions in
 * flight as a stack; and a question answered from what the store kept is not told of, so a listener
 * hears of work and of nothing else.
 */
class AStoreTellsWhichQuestionItIsWorkingOutTest {

    private static final String MODEL = """
            module told.model

            data Low = { n: Int }
            data High = { n: Int }

            behavior sort : (n: Int) -> Low | High
                constructs Low, High
            let sort (n) = if n < 10 then Low { n = n } else High { n = n }

            behavior twice : (n: Int) -> Int
            let twice (n) = n + n

            example sort
                | "low"  : (1)  -> Low { n = 1 }
                | "high" : (20) -> High { n = 20 }

            example twice
                | "two" : (1) -> 2
            """;

    /** Keeps the questions in flight, and fails where an end is not the end of the innermost. */
    private static final class Nesting implements Answering {
        private final Deque<Key<?>> inFlight = new ArrayDeque<>();
        private final List<Key<?>> started = new ArrayList<>();

        @Override
        public void started(Key<?> key) {
            inFlight.push(key);
            started.add(key);
        }

        @Override
        public void finished(Key<?> key) {
            assertSame(inFlight.pop(), key, "the working out that ended is the innermost begun");
        }

        @Override
        public void startedOn(String module, String behavior) {
            assertTrue(!inFlight.isEmpty(), "a part is a part of a question in flight");
        }

        @Override
        public void finishedOn(String module, String behavior) {
        }
    }

    private static Compilation measured() {
        Compilation compilation = Compilation.ofSource(MODEL, "told.model");
        compilation.measure(Adequacy.Asked.fullReport());
        return compilation;
    }

    @Test
    void theCallsNestAsTheQuestionsDoAndEachQuestionWorkedOutIsToldOfOnce() {
        Compilation compilation = measured();
        Nesting told = new Nesting();
        compilation.tell(told);

        compilation.answerEverything();

        assertEquals(List.of(), compilation.errors().stream().map(Object::toString).toList());
        assertTrue(told.inFlight.isEmpty(), "every working out begun has ended");
        assertTrue(told.started.size() > 1, "the measurement was worked out while listened to");
        assertEquals(told.started.size(), new LinkedHashSet<>(told.started).size(),
                "a question is worked out once");
    }

    @Test
    void aQuestionAnsweredFromWhatTheStoreKeptIsNotToldOf() {
        Compilation compilation = measured();
        compilation.answerEverything();
        Nesting told = new Nesting();
        compilation.tell(told);

        compilation.answerEverything();

        assertEquals(List.of(), told.started);
    }

    @Test
    void whatIsWorkedOnIsEachBehaviorMeasuredAndNothingOnceTheRunHasEnded() {
        Compilation compilation = measured();
        WhatIsBeingMeasured where = new WhatIsBeingMeasured();
        Set<WhatIsBeingMeasured.Subject> seen = new LinkedHashSet<>();
        compilation.tell(new Answering() {
            @Override
            public void started(Key<?> key) {
                where.started(key);
                where.now().map(WhatIsBeingMeasured.Work::asked).ifPresent(seen::add);
            }

            @Override
            public void finished(Key<?> key) {
                where.finished(key);
            }

            @Override
            public void startedOn(String module, String behavior) {
                where.startedOn(module, behavior);
            }

            @Override
            public void finishedOn(String module, String behavior) {
                where.finishedOn(module, behavior);
            }
        });

        compilation.answerEverything();

        assertEquals(Optional.empty(), where.now());
        for (String behavior : List.of("sort", "twice")) {
            assertTrue(seen.contains(new WhatIsBeingMeasured.Subject("told.model",
                    Optional.of(behavior))), behavior + " among " + seen);
        }
    }

    /** A question about one behavior that asks one about another on its way. */
    private record AboutOne(String name, String behavior, Optional<String> asksOf)
            implements Key<Optional<WhatIsBeingMeasured.Work>> {

        static WhatIsBeingMeasured where;

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Optional<WhatIsBeingMeasured.Work>> compute(Db db) {
            return asksOf.isPresent()
                    ? db.ask(new AboutOne(name, asksOf.get(), Optional.empty()))
                    : Answer.of(where.now());
        }
    }

    private static WhatIsBeingMeasured.Subject behavior(String name) {
        return new WhatIsBeingMeasured.Subject("told.model", Optional.of(name));
    }

    @Test
    void theWorkIsForTheOutermostBehaviorAskedAboutAndReadsTheInnermost() {
        Compilation compilation = measured();
        ACompiledModel.compiles(compilation);
        AboutOne.where = new WhatIsBeingMeasured();
        compilation.tell(AboutOne.where);

        Optional<WhatIsBeingMeasured.Work> alone = compilation.db()
                .ask(new AboutOne("told.model", "sort", Optional.empty())).value();
        Optional<WhatIsBeingMeasured.Work> forAnother = compilation.db()
                .ask(new AboutOne("told.model", "sort", Optional.of("twice"))).value();

        assertEquals(Optional.of(new WhatIsBeingMeasured.Work(behavior("sort"),
                behavior("sort"))), alone);
        assertEquals(Optional.of(new WhatIsBeingMeasured.Work(behavior("sort"),
                behavior("twice"))), forAnother);
    }

    /** A question about a module that goes through its behaviors in turn. */
    private record AboutTheModule(String name, List<String> behaviors)
            implements Key<List<Optional<WhatIsBeingMeasured.Work>>> {

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<List<Optional<WhatIsBeingMeasured.Work>>> compute(Db db) {
            List<Optional<WhatIsBeingMeasured.Work>> out = new ArrayList<>();
            for (String behavior : behaviors) {
                out.add(db.onOneBehavior(name, behavior, AboutOne.where::now));
            }
            out.add(AboutOne.where.now());
            return Answer.of(out);
        }
    }

    @Test
    void aQuestionAboutAModuleSaysWhichOfItsBehaviorsItIsOn() {
        Compilation compilation = measured();
        ACompiledModel.compiles(compilation);
        AboutOne.where = new WhatIsBeingMeasured();
        compilation.tell(AboutOne.where);
        WhatIsBeingMeasured.Subject module =
                new WhatIsBeingMeasured.Subject("told.model", Optional.empty());

        List<Optional<WhatIsBeingMeasured.Work>> seen = compilation.db()
                .ask(new AboutTheModule("told.model", List.of("sort", "twice"))).value();

        assertEquals(List.of(
                Optional.of(new WhatIsBeingMeasured.Work(behavior("sort"), behavior("sort"))),
                Optional.of(new WhatIsBeingMeasured.Work(behavior("twice"), behavior("twice"))),
                Optional.of(new WhatIsBeingMeasured.Work(module, module))), seen);
    }

    @Test
    void theBehaviorsToBeMeasuredAreTheOnesTheBuildChose() {
        Compilation everything = measured();
        assertEquals(Map.of("told.model", List.of("sort", "twice")),
                WhatIsBeingMeasured.toBeMeasuredIn(everything));

        Compilation one = measured();
        one.choose(new Adequacy.Choice(null, "twice"));
        assertEquals(Map.of("told.model", List.of("twice")),
                WhatIsBeingMeasured.toBeMeasuredIn(one));
    }
}
