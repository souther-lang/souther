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
 * <p>Which catalog entry a message renders through, and which code it reports, are read off the
 * message's own type — {@link MessageKeys} for the first, {@link Code} for the second. Neither is a
 * string a site chooses, so two messages cannot name one entry and a message cannot name none.
 *
 * <p>A value the reader should not see is not a component: a position is a {@code Region}, a value
 * shown only in a hint belongs to the hint's own message, and a wording that turns on a value is two
 * messages rather than one entry that selects between two sentences.
 */
public sealed interface Message permits AttemptMessage, CodecMessage, DataMessage, ExampleMessage, HelperMessage,
        ImportMessage, InjectionMessage, InvariantMessage, MatchMessage, ModuleMessage,
        TypeMessage {

    /**
     * The catalog entry this renders through, read off where the message is declared.
     *
     * <p>Named for what it answers rather than {@code key}, because a record's component of that
     * name would override it: a message about a map key carried one, and every reader of it was
     * answered the key's value where the entry's name was meant. The build refuses a component that
     * takes this name.
     */
    default String entry() {
        return MessageKeys.of(getClass());
    }
}
