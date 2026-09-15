package souther.compiler.types;

/**
 * Something this compile keeps about how it built what it built: which construct of a source a
 * thing was written as, why a pass put an application where one stands, what a name was expanded
 * through, how a reference was numbered.
 *
 * <p>Not what a declaration says. What the front end settled about a declaration is
 * {@link SettledAnswer}, and these stand beside it — the same value said the same way by two builds
 * can carry two of these, because they say how each build arrived rather than what it arrived at.
 * The readers that want one want it as an identity: the coverage that files what a row exercised,
 * the reports that say which construct a reason is about.
 *
 * <p>Saying so is not saying what any reader does with it. A reader that holds two builds to each
 * other can pass over one, read it, or read part of it, and which of those it is is decided where
 * that reading is written. Being a record of the building is what a type is; being read is what
 * happens to it.
 */
public interface RecordOfTheBuilding {
}
