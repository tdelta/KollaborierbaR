import ObligationResult from './ObligationResult';
import OpenGoalInfo from './OpenGoalInfo';

// define the structure of received KeY results
export default interface ProofResults {
  succeeded: ObligationResult[];
  failed: ObligationResult[];
  errors: ObligationResult[];
  stackTraces: ObligationResult[];
}
