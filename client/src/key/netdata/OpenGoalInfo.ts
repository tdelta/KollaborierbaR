/**
 * When running a proof on the backend server, it returns information on still
 * open proofs as a data structure, which conforms to this interface.
 *
 * See the documentation of the OpenGoalInfo class of the backend server for more
 * information on the members of this interface.
 *
 * Instances of this interface are usually stored as part of {@link ObligationResult}
 */
export default interface OpenGoalInfo {
  id: number;
  sequent: string;
  formula: string;
}
