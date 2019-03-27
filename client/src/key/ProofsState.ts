import ObligationResult, {
  ObligationResultKind,
} from './netdata/ObligationResult';

import ObligationResultHistory from './ObligationResultHistory';

import ProofNode from './prooftree/ProofNode';

/**
 * This class is used, to make all proofs available at the backend server for
 * the currently opened file accessible to the application UI.
 * It is refreshed by {@link KeYInterface}/{@link ProofSyncController}.
 *
 * For more information on the stored data, see the documentation of
 * {@link ObligationResultHistory} and the ProofController class documentation
 * of the backend server.
 *
 * This class is designed, such that its instances are to be treated as
 * immutable (though it does reuse objects internally, so its "pseudo-immutable").
 * This is because it is meant to be used as part of the application's main React
 * state. Manipulations to this state are easier to manage with immutable objects.
 *
 * It contains a number of useful methods for queries about the state of available
 * proofs.
 */
export default class ProofsState {
  /** maps each proof obligation of the current file by index to its proof history */
  private obligationResults: Map<number, ObligationResultHistory>;

  private constructor(obligationResults: Map<number, ObligationResultHistory>) {
    this.obligationResults = obligationResults;

    this.allGoalsAreClosed = this.allGoalsAreClosed.bind(this);
    this.getHistoryByObligationIdx = this.getHistoryByObligationIdx.bind(this);
    this.getAllRecentObligationResults = this.getAllRecentObligationResults.bind(
      this
    );
    this.getAllRecentTrees = this.getAllRecentTrees.bind(this);
    this.getProvenObligationIdxs = this.getProvenObligationIdxs.bind(this);
    this.updateLastResultByObligationIdx = this.updateLastResultByObligationIdx.bind(
      this
    );
    this.updateSavedResultsByObligationIdx = this.updateSavedResultsByObligationIdx.bind(
      this
    );
  }

  /**
   * Factory method for creating empty instances of this class.
   */
  public static create(): ProofsState {
    return new ProofsState(new Map());
  }

  /**
   * Indicates, whether all goals in all proofs stored are closed.
   */
  public allGoalsAreClosed(): boolean {
    return !this.getAllRecentObligationResults().some(
      (obligationResult: ObligationResult) =>
        obligationResult.openGoals.length > 0
    );
  }

  /**
   * Get the proof history and lates proof for a specific proof obligation.
   *
   * @param idx - index of the proof obligation, counted from top to bottom of
   *              the current file.
   */
  public getHistoryByObligationIdx(
    idx: number
  ): ObligationResultHistory | undefined {
    return this.obligationResults.get(idx);
  }

  /**
   * Get the most recent available proof results of all proof obligations.
   */
  public getAllRecentObligationResults(): ObligationResult[] {
    return Array.from(this.obligationResults.values())
      .map((history: ObligationResultHistory) => history.last)
      .filter(
        (obligationResult?: ObligationResult) => obligationResult != null
      ) as ObligationResult[];
  }

  /**
   * Returns the number of proof obligations, for which proofs are available.
   */
  public numOfObligationsWithAvailableProofs(): number {
    return Array.from(this.obligationResults.keys()).length;
  }

  /**
   * Get the most recent available proof trees of all proof obligations.
   */
  public getAllRecentTrees(): ProofNode[] {
    return this.getAllRecentObligationResults()
      .map((obligationResult: ObligationResult) => obligationResult.proofTree)
      .filter((proofTree?: ProofNode) => proofTree != null) as ProofNode[];
  }

  /**
   * Get the indices counted from top to bottom of the Java source file for all
   * proof obligations with available, successful proofs.
   */
  public getProvenObligationIdxs(): number[] {
    return this.getAllRecentObligationResults()
      .filter(
        obligationResult =>
          obligationResult.kind === ObligationResultKind.success
      )
      .map(obligationResult => obligationResult.obligationIdx);
  }

  /**
   * Registers a new proof result as the most recent result for a proof obligation.
   *
   * Always use the new returned {@link ProofsState} instance for all further
   * processing.
   *
   * @param idx - index of the proof obligation, counted from top to bottom of
   *              the current file.
   * @param result - new most recent result
   * @returns updated state
   */
  public updateLastResultByObligationIdx(
    idx: number,
    result: ObligationResult
  ): ProofsState {
    const obligationResults = this.obligationResults;
    const prevHistory = obligationResults.get(idx);

    let saved: ObligationResult[];
    if (prevHistory == null) {
      saved = [];
    } else {
      saved = prevHistory.saved;
    }

    obligationResults.set(idx, new ObligationResultHistory(idx, result, saved));

    return new ProofsState(obligationResults);
  }

  /**
   * Registers an updated proof history for a proof obligation.
   *
   * Always use the new returned {@link ProofsState} instance for all further
   * processing.
   *
   * @param idx - index of the proof obligation, counted from top to bottom of
   *              the current file.
   * @param savedObligationResults - new history
   * @returns updated state
   */
  public updateSavedResultsByObligationIdx(
    idx: number,
    savedObligationResults: ObligationResult[]
  ): ProofsState {
    const obligationResults = this.obligationResults;
    const prevHistory = obligationResults.get(idx);

    let last: ObligationResult | undefined;
    if (prevHistory != null) {
      last = prevHistory.last;
    }

    obligationResults.set(
      idx,
      new ObligationResultHistory(idx, last, savedObligationResults)
    );

    return new ProofsState(obligationResults);
  }
}
