package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.ElementBindings;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A watch asked what it read, and what readings inside it and readings taken again asked, answers
 * the same whether those names are shared between watches or written out for each.
 *
 * <p>The reference here is the reading as it was written when each watch held a table of the
 * names and what it was answered, and placed every entry of a table it took in, one by one, against
 * where the watch began. Random trees of applications, and readings that read, are watched inside
 * one another, ended and taken again, in places on the way from where a watch began, apart from it
 * and before it. What each says of whether it is told apart by what it asked, and which of a set
 * of other environments it holds of, is compared.
 */
class AWatchPassingItsNamesOnBySharingThemAnswersAsTheTableItReplacedDidTest {

    private static final SourcePos POS = new SourcePos(1, 1);
    private static final BindingOwner OWNER = new BindingOwner.OfValue("demo", "go");
    private static final List<BindingId> NAMES = List.of(new BindingId(OWNER, 0),
            new BindingId(OWNER, 1), new BindingId(OWNER, 2), new BindingId(OWNER, 3));

    /** An application as the test made it, beside the environment it made. */
    private record Env(BindingEnvironment real, Env parent, BindingId step,
                       Map<BindingId, Long> values) {

        Env handing(BindingId name, long value) {
            Map<BindingId, Long> wider = new LinkedHashMap<>(values);
            wider.put(name, value);
            return new Env(real.handing(name, new Core.Int(value, Type.INT, POS)), this, name,
                    wider);
        }
    }

    private sealed interface Act {}

    private record Read(Env in, BindingId name) implements Act {}

    private record Nested(Env on, List<Act> body) implements Act {}

    private record Replay(Env at, int which) implements Act {}

    /** What the reference says a watch asked. */
    private record RefAnswers(Map<BindingId, Long> answers, boolean toldApart) {}

    private static final class RefWatch {
        final Env started;
        final Map<BindingId, Long> asked = new LinkedHashMap<>();
        boolean unsure;

        RefWatch(Env started) {
            this.started = started;
        }

        /** The three places a read can stand, as the tables placed them. */
        private static String placing(Env in, Env began, BindingId name) {
            boolean handedSince = false;
            for (Env each = in; each != null; each = each.parent()) {
                if (each == began) {
                    return handedSince ? "SINCE" : "BEGUN";
                }
                handedSince |= name.equals(each.step());
            }
            return "OFF";
        }

        void read(Env in, BindingId name) {
            switch (placing(in, started, name)) {
                case "BEGUN" -> asked.putIfAbsent(name, in.values().get(name));
                case "SINCE" -> { }
                default -> unsure = true;
            }
        }

        void note(Env in, Map<BindingId, Long> answers, boolean notTold) {
            if (notTold) {
                unsure = true;
            }
            for (Map.Entry<BindingId, Long> each : answers.entrySet()) {
                switch (placing(in, started, each.getKey())) {
                    case "BEGUN" -> asked.putIfAbsent(each.getKey(), each.getValue());
                    case "SINCE" -> { }
                    default -> unsure = true;
                }
            }
        }
    }

    private final Random random = new Random(3219);

    private Env someEnv(List<Env> pool) {
        return pool.get(random.nextInt(pool.size()));
    }

    private List<Act> body(List<Env> pool, int depth) {
        List<Act> acts = new ArrayList<>();
        for (int i = random.nextInt(5); i >= 0; i--) {
            int kind = random.nextInt(depth > 0 ? 6 : 4);
            if (kind < 3) {
                acts.add(new Read(someEnv(pool), NAMES.get(random.nextInt(NAMES.size()))));
            } else if (kind == 3) {
                acts.add(new Replay(someEnv(pool), random.nextInt(8)));
            } else {
                acts.add(new Nested(someEnv(pool), body(pool, depth - 1)));
            }
        }
        return acts;
    }

    private static HandedAnswers real(Env on, List<Act> body, List<HandedAnswers> made) {
        return BindingEnvironment.Watch.over(on.real(), () -> {
            for (Act each : body) {
                switch (each) {
                    case Read r -> r.in().real().roleOf(r.name());
                    case Nested n -> made.add(real(n.on(), n.body(), made));
                    case Replay p -> {
                        HandedAnswers again = made.isEmpty() ? null
                                : made.get(p.which() % made.size());
                        if (again != null && (!again.toldApart()
                                || again.holdsOf(p.at().real()))) {
                            BindingEnvironment.Watch.replay(p.at().real(), again);
                        }
                    }
                }
            }
            return 0;
        }).asked();
    }

    private static RefAnswers reference(Env on, List<Act> body, RefWatch outer,
                                        List<RefAnswers> made) {
        RefWatch watch = new RefWatch(on);
        for (Act each : body) {
            switch (each) {
                case Read r -> watch.read(r.in(), r.name());
                case Nested n -> made.add(reference(n.on(), n.body(), watch, made));
                case Replay p -> {
                    RefAnswers answers = made.isEmpty() ? null
                            : made.get(p.which() % made.size());
                    if (answers != null && (!answers.toldApart() || holds(answers, p.at()))) {
                        watch.note(p.at(), answers.answers(), !answers.toldApart());
                    }
                }
            }
        }
        if (outer != null) {
            outer.note(on, watch.asked, watch.unsure);
        }
        return watch.unsure ? new RefAnswers(Map.of(), false)
                : new RefAnswers(watch.asked, true);
    }

    private static boolean holds(RefAnswers answers, Env candidate) {
        if (!answers.toldApart()) {
            return false;
        }
        for (Map.Entry<BindingId, Long> each : answers.answers().entrySet()) {
            if (!Objects.equals(each.getValue(), candidate.values().get(each.getKey()))) {
                return false;
            }
        }
        return true;
    }

    @Test
    void whatEachSaysOfWhichEnvironmentsItHoldsOfIsWhatTheTablesSaid() {
        int told = 0;
        int untold = 0;
        for (int trial = 0; trial < 500; trial++) {
            List<Env> pool = new ArrayList<>();
            Env root = new Env(new BindingEnvironment(Map.of(), Map.of(), ElementBindings.NONE,
                    ValueDefinitions.NONE, false), null, null, Map.of());
            pool.add(root);
            for (int i = random.nextInt(8) + 1; i > 0; i--) {
                pool.add(someEnv(pool).handing(NAMES.get(random.nextInt(NAMES.size())),
                        random.nextInt(3)));
            }
            Env on = someEnv(pool);
            List<Act> body = body(pool, 3);

            List<HandedAnswers> madeReal = new ArrayList<>();
            HandedAnswers real = real(on, body, madeReal);
            List<RefAnswers> madeReference = new ArrayList<>();
            RefAnswers reference = reference(on, body, null, madeReference);

            assertEquals(reference.toldApart(), real.toldApart(), "told apart, trial " + trial);
            for (Env candidate : pool) {
                assertEquals(holds(reference, candidate), real.holdsOf(candidate.real()),
                        "holds of an environment, trial " + trial);
            }
            for (int i = 0; i < madeReal.size(); i++) {
                assertEquals(madeReference.get(i).toldApart(), madeReal.get(i).toldApart(),
                        "inner told apart, trial " + trial + " reading " + i);
                for (Env candidate : pool) {
                    assertEquals(holds(madeReference.get(i), candidate),
                            madeReal.get(i).holdsOf(candidate.real()),
                            "inner holds, trial " + trial + " reading " + i);
                }
            }
            if (real.toldApart()) {
                told++;
            } else {
                untold++;
            }
        }
        // Both ways the readings came out are met, or what was compared is one answer.
        assertEquals(true, told > 50 && untold > 50, "told " + told + ", untold " + untold);
    }
}
