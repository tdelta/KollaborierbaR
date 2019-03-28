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
