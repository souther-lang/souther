package souther.compiler.diag.msg;

import souther.compiler.diag.DiagnosticCode;

/** What a behavior implemented outside this module is told about what it may name. */
public sealed interface InjectionMessage extends Message {

    /** An injected behavior's input rests on a type the module keeps to itself. */
    @Code(DiagnosticCode.E1612)
    record AnInjectedInputRestsOnWhatIsKept(String behavior, String kept)
            implements InjectionMessage {}

    /** The same, of its output. */
    @Code(DiagnosticCode.E1612)
    record AnInjectedOutputRestsOnWhatIsKept(String behavior, String kept)
            implements InjectionMessage {}

    /** Why an injected behavior is held to it whatever `exposing` says. */
    @Code(DiagnosticCode.E1612)
    record TheBaseClassIsPublicWhateverExposingSays(String kept) implements InjectionMessage {}
}
