import ProofNode from '../prooftree/ProofNode';

import OpenGoalInfo from './OpenGoalInfo';

export default interface ObligationResult {
  obligationIdx: number;
  targetName: string;
  resultMsg: string;
  proofTree: ProofNode;
  openGoals: OpenGoalInfo[];
  kind: ObligationResultKind;
}

export enum ObligationResultKind {
  success = 'success',
  failure = 'failure',
  error = 'error'
}
