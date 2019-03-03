import ProofNode from '../prooftree/ProofNode';

export default interface ObligationResult {
  obligationIdx: number;
  resultMsg: string;
  proofTree: ProofNode;
}
