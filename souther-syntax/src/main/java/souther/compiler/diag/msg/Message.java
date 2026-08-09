package souther.compiler.diag.msg;

/**
 * What a diagnostic says, as the values it is about.
 *
 * <p>A message is a record whose components are those values, and the catalog entry it renders
 * through names each of them: {@code Field `{field}` from `...{from}` conflicts with the one
 * `{heldBy}` supplies.} The build holds every message to saying all of them, in every shipped
 * language, so a value a diagnostic carries is a value its reader is shown. Carrying one and not
 * showing it is not expressible.
 *
 * <p>Which catalog entry a message renders through is read off the message's own type
 * ({@link MessageKeys}), so it is not a string a site chooses, two messages cannot name one entry
 * and a message cannot name none. Which rule it reports is read the same way ({@link MessageCodes}),
 * of the messages that report one: those are {@link Reported}, and a hint or a secondary label is
 * not.
 *
 * <p>Both are functions of the type and not methods here. A record component generates an accessor,
 * so a method on this interface is one a message could answer for itself: a component named
 * {@code key} once answered every reader asking which entry to render, and a component named
 * {@code reports} would have let a site report whatever code it was handed. What is declared here is
 * nothing, so there is nothing for a component to stand in front of.
 *
 * <p>A value the reader should not see is not a component: a position is a {@code Region}, a value
 * shown only in a hint belongs to the hint's own message, and a wording that turns on a value is two
 * messages rather than one entry that selects between two sentences.
 */
public sealed interface Message permits ArithmeticMessage, AttemptMessage, BehaviorMessage,
        CodecMessage, DataMessage, DeclarationMessage, ExampleMessage, HelperMessage, ImportMessage,
        InjectionMessage, InvariantMessage, MatchMessage, ModuleMessage, NameMessage, ParseMessage,
        Reported, TypeMessage {
}
