package souther.compiler.reading;

import souther.compiler.coverage.UnreachableReasons;

import java.util.List;

/**
 * A part of a body that answers no value, with what holds of the inputs on every way a run comes to
 * it.
 *
 * <p>The largest such part on the way down and not each {@code unreachable} inside it. A
 * {@code match} every arm of which aborts answers nothing as a whole, and a run that reaches it
 * aborts whichever arm it takes — so what is true of the inputs that get there is said by the ways
 * to the {@code match}, and asking it of each arm would need the arms put back together to say it.
 *
 * <p>Only where every way to it is named. A way this reading could not state is one a row cannot
 * be steered along or kept off, so a part reached by one says nothing here about which inputs
 * reach it.
 *
 * <p>Conditions and not {@link WayIn}s. A way in carries what a run that came it would be seen to
 * have done, and an arm that answers nothing is one nothing watches — no run through it is recorded
 * — while what it takes of the inputs is the case it is written for all the same. That half is all
 * this is about.
 *
 * <p>What it says is what the body does and not what the model may be asked. An {@code unreachable}
 * is a statement that the inputs reaching it do not arise; whether anything proves that is the
 * claim's question, and none of it is decided here.
 *
 * @param ways every way a run arrives here, each the conditions that hold on it together; a run on
 *             any of them answers nothing
 * @param said the reasons the {@code unreachable}s a run here aborts at give, in the order evaluation
 *             reaches them
 */
public record NothingAnsweredHere(List<List<Condition>> ways, List<UnreachableReasons.Said> said) {

    public NothingAnsweredHere {
        ways = ways.stream().<List<Condition>>map(List::copyOf).toList();
        said = List.copyOf(said);
        if (ways.isEmpty()) {
            throw new IllegalArgumentException("a part a run comes to is come to some way");
        }
    }
}
