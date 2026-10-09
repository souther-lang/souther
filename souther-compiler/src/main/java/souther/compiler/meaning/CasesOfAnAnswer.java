package souther.compiler.meaning;

import souther.compiler.inputs.TermPath;
import souther.compiler.types.TypeSymbol;

import java.util.List;
import java.util.Objects;
import java.util.Set;

/**
 * Which case a behavior's answer is, read once off its body over its own parameters.
 *
 * <p>Said of the definition and of no call. What a body answers, and under which conditions, is the
 * same whoever calls it; what differs from call to call is what each parameter was handed, and that
 * is put in where a call is read ({@link Derivation.ABehaviorsAnswerAtACall}). Read at each call
 * instead, one body would be read once per call, and two calls handing it different values would
 * file what its conditions state under the same constructs of the model.
 *
 * <p>Only which case the answer is, and nothing else it might be asked: a call whose answer is
 * matched on is asked that, and what the answer holds is a question of what the body computes.
 *
 * @param parameters the names the body reads its parameters by, in the order a call hands them
 * @param answered   which case the body answers, and where
 */
public record CasesOfAnAnswer(List<String> parameters, Answered answered) {

    public CasesOfAnAnswer {
        parameters = List.copyOf(parameters);
        Objects.requireNonNull(answered, "a body answers something");
    }

    /** Which case a value a body answers is. */
    public sealed interface Answered {

        /** One of {@code cases}, whatever the input: a value the body writes out, or a name standing
         *  for one of several it does. */
        record Written(Set<TypeSymbol> cases) implements Answered {

            public Written {
                cases = Set.copyOf(cases);
                if (cases.isEmpty()) {
                    throw new IllegalArgumentException("a value written out is of some case");
                }
            }
        }

        /** What stands at {@code at} of the body's own input, whichever case that is. */
        record AtAnInput(TermPath at) implements Answered {

            public AtAnInput {
                Objects.requireNonNull(at, "a value of the input stands somewhere");
            }
        }

        /** Not read, and why. */
        record Unread(WhyUnread why) implements Answered {

            public Unread {
                Objects.requireNonNull(why, "a value is left unread for some reason");
            }
        }

        /**
         * One of several values, each answered where the body reaches it. The arms exclude each
         * other: each holds of a run that takes it and of no other.
         */
        record ByItsArms(List<Arm> arms) implements Answered {

            public ByItsArms {
                arms = List.copyOf(arms);
                if (arms.isEmpty()) {
                    throw new IllegalArgumentException("a value chosen by arms has an arm");
                }
            }
        }

        /**
         * One arm: where a run reaches it, over the body's own input, and what it answers there.
         *
         * @param reached whether a run takes this arm, every arm before it written in
         */
        record Arm(Derivation reached, Answered answers) {

            public Arm {
                Objects.requireNonNull(reached, "an arm is reached somewhere");
                Objects.requireNonNull(answers, "an arm answers something");
            }
        }
    }
}
