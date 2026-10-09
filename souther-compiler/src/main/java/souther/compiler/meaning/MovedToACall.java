package souther.compiler.meaning;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

/**
 * What a behavior's body states over its own parameters, said of what one call handed them.
 *
 * <p>Each place of the body's input is a parameter and a way into it; at a call, the same way into
 * whatever the call handed that parameter is the same value. So a statement is moved by moving each
 * place it is about, and nothing else about it changes.
 *
 * <p>A part about something a call cannot say — a parameter handed a value at no position, what the
 * body's own dependency answers, a value the body binds for itself — is left unread for that
 * reason, at the smallest statement it is in. The statements beside it are moved as they are.
 */
final class MovedToACall {

    private final Map<String, TermPath> handed;
    private final Function<WhyUnread, Proposition> unread;

    /**
     * @param handed which position of the caller's input each parameter was handed, by the name
     *               the body reads it by; a parameter handed anything else is not in it
     * @param unread a part left unread for a reason, as the reading concluding it numbers one
     */
    private MovedToACall(Map<String, TermPath> handed, Function<WhyUnread, Proposition> unread) {
        this.handed = Map.copyOf(handed);
        this.unread = unread;
    }

    /** {@code stated}, of what the call handed each parameter ({@link MovedToACall}). */
    static Proposition of(Proposition stated, Map<String, TermPath> handed,
                          Function<WhyUnread, Proposition> unread) {
        return new MovedToACall(handed, unread).moved(stated);
    }

    /**
     * Something moved, or why it could not be: something a call cannot say, or a number the moved
     * statement could not be held in.
     */
    private record Moved<T>(T value, WhyUnread stopped) {

        static <T> Moved<T> to(T value) {
            return new Moved<>(value, null);
        }

        static <T> Moved<T> stoppedBy(WhyUnread.InACalledBody.What why) {
            return new Moved<>(null, new WhyUnread.InACalledBody(why));
        }

        /** Stopped for {@code why}: what a statement moved inside it says stopped that, or a
         *  number the moved statement could not be held in. */
        static <T> Moved<T> stoppedFor(WhyUnread why) {
            return new Moved<>(null, why);
        }

        /** Stopped where {@code part} of it was, for the same reason. */
        static <T> Moved<T> stoppedAt(Moved<?> part) {
            return new Moved<>(null, part.stopped());
        }
    }

    private Proposition moved(Proposition stated) {
        return switch (stated) {
            case Proposition.Always always -> always;
            case Proposition.Unread read -> read;
            case Proposition.Compared(Relation relation, boolean holds, var _) ->
                    compared(relation, holds);
            case Proposition.Truth(DecisionSubject of, boolean holds, var _) ->
                    stated(subject(of), at -> new Proposition.Truth(at, holds));
            case Proposition.InCases(DecisionSubject of, var cases, boolean holds, var _) ->
                    stated(subject(of), at -> new Proposition.InCases(at, cases, holds));
            case Proposition.Present(DecisionSubject of, boolean holds, var _) ->
                    stated(subject(of), at -> new Proposition.Present(at, holds));
            case Proposition.SameValue(DecisionSubject one, DecisionSubject other, boolean holds,
                                       var _) -> {
                Moved<DecisionSubject> first = subject(one);
                Moved<DecisionSubject> second = subject(other);
                yield first.stopped() != null ? unread(first.stopped())
                        : second.stopped() != null ? unread(second.stopped())
                        : new Proposition.SameValue(first.value(), second.value(), holds);
            }
            case Proposition.All all -> Proposition.all(all.parts().stream()
                    .map(this::moved).toList());
            case Proposition.Any any -> Proposition.any(any.parts().stream()
                    .map(this::moved).toList());
            case Proposition.OnAnApplication applications -> Proposition.onAnApplication(
                    applications.each().stream().map(this::moved).toList());
            case Proposition.Some(TermPath container, Proposition ofTheElement, boolean holds,
                                  var _) -> stated(path(container),
                    at -> new Proposition.Some(at, moved(ofTheElement), holds));
        };
    }

    private Proposition unread(WhyUnread why) {
        return unread.apply(why);
    }

    private <T> Proposition stated(Moved<T> moved, Function<T, Proposition> stating) {
        return moved.stopped() != null ? unread(moved.stopped()) : stating.apply(moved.value());
    }

    private Proposition compared(Relation relation, boolean holds) {
        return switch (relation) {
            case Relation.Affine(LinearForm<Quantity> form, var proposition) -> {
                Moved<LinearForm<Quantity>> to = form(form);
                if (to.stopped() != null) {
                    yield unread(to.stopped());
                }
                Relation.OneWay<Quantity> one = Relation.OneWay.of(to.value(), proposition);
                yield new Proposition.Compared(new Relation.Affine(one.form(), one.proposition()),
                        holds == one.holds());
            }
            case Relation.Ordered(DecisionAtom term, var at, var proposition) -> stated(atom(term),
                    to -> new Proposition.Compared(new Relation.Ordered(to, at, proposition),
                            holds));
        };
    }

    private Moved<LinearForm<Quantity>> form(LinearForm<Quantity> form) {
        List<LinearForm<Quantity>> terms = new ArrayList<>();
        terms.add(LinearForm.constant(form.constant()));
        for (Map.Entry<Quantity, ExactRatio> each : form.coefs().entrySet()) {
            Moved<Quantity> atom = quantity(each.getKey());
            if (atom.stopped() != null) {
                return Moved.stoppedAt(atom);
            }
            terms.add(LinearForm.weighing(atom.value(), each.getValue()));
        }
        // Two parameters handed one position are one number there, so their weights add — all at
        // once, so whether they are held does not turn on which parameter came first.
        return switch (LinearForm.sum(terms)) {
            case ExactAnswer.Held<LinearForm<Quantity>> held -> Moved.to(held.value());
            case ExactAnswer.Unheld<LinearForm<Quantity>> unheld ->
                    Moved.stoppedFor(new WhyUnread.ANumberNotHeld(unheld.why()));
        };
    }

    private Moved<DecisionAtom> atom(DecisionAtom atom) {
        return switch (atom) {
            case DecisionAtom.OfTheInput(NumericTerm term) -> {
                if (!handed.containsKey(term.subjectPath().head())) {
                    yield Moved.stoppedBy(WhyUnread.InACalledBody.What.AN_ARGUMENT_AT_NO_POSITION);
                }
                NumericTerm to = term.movedTo(this::placed);
                yield to == null
                        ? Moved.stoppedBy(WhyUnread.InACalledBody.What.AN_ARGUMENT_AT_NO_POSITION)
                        : Moved.to(new DecisionAtom.OfTheInput(to));
            }
            case DecisionAtom.OfAnAnswer _ ->
                    Moved.stoppedBy(WhyUnread.InACalledBody.What.WHAT_ITS_DEPENDENCY_ANSWERS);
        };
    }

    private Moved<Quantity> quantity(Quantity atom) {
        return switch (atom) {
            case DecisionAtom decided -> {
                Moved<DecisionAtom> to = atom(decided);
                yield to.stopped() != null ? Moved.stoppedAt(to) : Moved.to(to.value());
            }
            case Quantity.OfABinding _ ->
                    Moved.stoppedBy(WhyUnread.InACalledBody.What.A_VALUE_IT_BINDS);
            case Quantity.HowManyMeet(TermPath container, Proposition ofTheElement) -> {
                Moved<TermPath> at = path(container);
                Proposition each = moved(ofTheElement);
                if (at.stopped() != null) {
                    yield Moved.stoppedAt(at);
                }
                // A count of what an element meets, where what it meets stopped at the call, is
                // no number: it stopped for what the statement says stopped it.
                WhyUnread stop = Proposition.firstStopIn(each);
                yield stop != null ? Moved.stoppedFor(stop)
                        : Moved.to(new Quantity.HowManyMeet(at.value(), each));
            }
            case Quantity.HowManyHold(List<Proposition> each) -> {
                List<Proposition> out = new ArrayList<>();
                for (Proposition one : each) {
                    Proposition to = moved(one);
                    WhyUnread stop = Proposition.firstStopIn(to);
                    if (stop != null) {
                        yield Moved.stoppedFor(stop);
                    }
                    out.add(to);
                }
                yield Moved.to(new Quantity.HowManyHold(out));
            }
        };
    }

    private Moved<DecisionSubject> subject(DecisionSubject of) {
        return switch (of) {
            case DecisionSubject.AnInput(TermPath at) -> {
                Moved<TermPath> to = path(at);
                yield to.stopped() != null ? Moved.stoppedAt(to)
                        : Moved.to(new DecisionSubject.AnInput(to.value()));
            }
            case DecisionSubject.AnAnswer _ ->
                    Moved.stoppedBy(WhyUnread.InACalledBody.What.WHAT_ITS_DEPENDENCY_ANSWERS);
        };
    }

    private Moved<TermPath> path(TermPath at) {
        return handed.containsKey(at.head()) ? Moved.to(placed(at))
                : Moved.stoppedBy(WhyUnread.InACalledBody.What.AN_ARGUMENT_AT_NO_POSITION);
    }

    /** {@code at}, a way into a parameter, as the same way into what the call handed it. */
    private TermPath placed(TermPath at) {
        return at.under(handed.get(at.head()));
    }
}
