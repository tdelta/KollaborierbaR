import ObligationResult, {ObligationResultKind} from './netdata/ObligationResult';
import ProofNode from './prooftree/ProofNode';

export default class ProofsState {
  private obligationResults: Map<number, ObligationResultHistory>;

  private constructor(obligationResults: Map<number, ObligationResultHistory>) {
    this.obligationResults = obligationResults;

    this.allGoalsAreClosed = this.allGoalsAreClosed.bind(this);
    this.getHistoryByObligationIdx = this.getHistoryByObligationIdx.bind(this);
    this.getAllRecentObligationResults = this.getAllRecentObligationResults.bind(this);
    this.getAllRecentTrees = this.getAllRecentTrees.bind(this);
    this.getProvenObligationIdxs = this.getProvenObligationIdxs.bind(this);
    this.updateLastResultByObligationIdx = this.updateLastResultByObligationIdx.bind(this);
    this.updateSavedResultsByObligationIdx = this.updateSavedResultsByObligationIdx.bind(this);
  }

  public static create(): ProofsState {
    return new ProofsState(new Map());
  }

  public allGoalsAreClosed(): boolean {
    return !this
      .getAllRecentObligationResults()
      .some((obligationResult: ObligationResult) => obligationResult.openGoals.length > 0);
  }

  public getHistoryByObligationIdx(idx: number): ObligationResultHistory | undefined {
    return this.obligationResults.get(idx);
  }

  public getAllRecentObligationResults(): ObligationResult[] {
    return Array.from(
        this
          .obligationResults
          .values()
      )
        .map((history: ObligationResultHistory) => history.last)
        .filter((obligationResult?: ObligationResult) => obligationResult != null) as ObligationResult[];
  }

  public getAllRecentTrees(): ProofNode[] {
    return this.getAllRecentObligationResults()
        .map((obligationResult: ObligationResult) => obligationResult.proofTree)
        .filter((proofTree?: ProofNode) => proofTree != null) as ProofNode[];
  }

  public getProvenObligationIdxs(): number[] {
    return this
      .getAllRecentObligationResults()
      .filter(obligationResult => obligationResult.kind === ObligationResultKind.success)
      .map(obligationResult => obligationResult.obligationIdx);
  }

  public updateLastResultByObligationIdx(idx: number, result: ObligationResult): ProofsState {
    const obligationResults = this.obligationResults;
    const prevHistory = obligationResults.get(idx);

    let saved: ObligationResult[];
    if (prevHistory == null) {
      saved = [];
    }

    else {
      saved = prevHistory.saved;
    }

    obligationResults.set(
      idx,
      new ObligationResultHistory(idx, result, saved)
    );

    return new ProofsState(
      obligationResults
    );
  }

  public updateSavedResultsByObligationIdx(idx: number, savedObligationResults: ObligationResult[]): ProofsState {
    const obligationResults = this.obligationResults;
    const prevHistory = obligationResults.get(idx);

    let last: ObligationResult | undefined = undefined
    if (prevHistory != null) {
      last = prevHistory.last;
    }

    obligationResults.set(
      idx,
      new ObligationResultHistory(idx, last, savedObligationResults)
    );

    return new ProofsState(
      obligationResults
    );
  }
}

export class ObligationResultHistory {
  private _obligationIdx: number;
  private _last: ObligationResult | undefined;
  private _saved: ObligationResult[];

  constructor(obligationIdx: number, last: ObligationResult | undefined, saved: ObligationResult[]) {
    this._obligationIdx = obligationIdx;
    this._last = last;
    this._saved = saved;
  }

  get obligationIdx(): number {
    return this._obligationIdx;
  }

  get last(): ObligationResult | undefined {
    return this._last;
  }

  get saved(): ObligationResult[] {
    return this._saved;
  }
}
