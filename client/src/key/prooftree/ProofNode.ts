/**
 * When running a proof on the backend server, it returns the resulting proof
 * tree as a recursive tree structure, whose nodes conform to this interface.
 *
 * See the documentation of the ProofNode class of the backend server for more
 * information on the members of this interface.
 *
 * Instances of this interface are usually stored as part of {@link ObligationResult}
 */
export default interface ProofNode {
  text: string;
  children: ProofNode[];
  kind: Kind;
  sequent: string;
  serialNr: number;
  oneStepId: number;
}

export enum Kind {
  OpenProofTree = 'OpenProofTree',
  ClosedProofTree = 'ClosedProofTree',
  BranchNode = 'BranchNode',
  OneStepSimplification = 'OneStepSimplification',
  OpenGoal = 'OpenGoal',
  ClosedGoal = 'ClosedGoal',
  InteractiveGoal = 'InteractiveGoal',
  LinkedGoal = 'LinkedGoal',
  DefaultNode = 'DefaultNode',
}
