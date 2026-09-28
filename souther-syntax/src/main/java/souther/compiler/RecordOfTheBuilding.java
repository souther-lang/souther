package souther.compiler;

/**
 * Something this compile keeps about reading a source and building what it built: where a thing was
 * written and how far the writing of it ran, which construct of the source it was written as, which
 * copy of a body a construct stands in, why a pass put an application where one stands, how a
 * reference was numbered.
 *
 * <p>Not what a declaration says. What the front end settled about a declaration is
 * {@link SettledAnswer}, and these stand beside it — two builds that say the same thing can carry
 * two of these, because they say how each arrived rather than what it arrived at. The readers that
 * want one want it as an identity: the coverage that files what a row exercised, the reports that
 * say which construct a reason is about, the readers that tell one copy of a spliced body from
 * another.
 *
 * <p>Saying so is not saying what any reader does with it. A reader that holds two builds to each
 * other can pass over one, read it, or read part of it, and which of those it is is decided where
 * that reading is written. Being a record of the building is what a form is; being read is what
 * happens to it.
 */
public interface RecordOfTheBuilding {
}
