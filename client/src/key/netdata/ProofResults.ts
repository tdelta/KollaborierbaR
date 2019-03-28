import ObligationResult from './ObligationResult';
import OpenGoalInfo from './OpenGoalInfo';

/**
 * When running proofs on the backend server, it returns the results as a data
 * structure, which conforms to this interface.
 *
 * See the documentation of the ProofResult class of the backend server for more
 * information on the members of this interface.
 */
export default interface ProofResults {
  succeeded: ObligationResult[];
  failed: ObligationResult[];
}
