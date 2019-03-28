import ProofNode from '../prooftree/ProofNode';

import OpenGoalInfo from './OpenGoalInfo';

/**
 * When running proofs on the backend server, it returns the results of a
 * single proof attempt as a data structure, which conforms to this interface.
 *
 * See the documentation of the ObligationResult class of the backend server for more
 * information on the members of this interface.
 *
 * Instances of this interface are usually stored as part of {@link ProofResults}
 */
export default interface ObligationResult {
  obligationIdx: number;
  targetName: string;
  resultMsg: string;
  proofTree: ProofNode;
  openGoals: OpenGoalInfo[];
  kind: ObligationResultKind;
  id: number;
}

export enum ObligationResultKind {
  success = 'success',
  failure = 'failure',
  error = 'error',
}
