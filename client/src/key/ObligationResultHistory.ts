import ObligationResult, {
  ObligationResultKind,
} from './netdata/ObligationResult';

/**
 * Represents proofs stored in the proof history at the server for a specific proof obligation.
 * It also stores the proof most recently run for that obligation.
 *
 * This class is used, to make the proof history accessible to the application
 * UI and is refreshed by {@link KeYInterface}/{@link ProofSyncController}.
 *
 * It is therefore a part of {@link ProofsState}
 *
 * For more information on the concept of proof history, see the documentation
 * of the ProofController class of the backend server.
 *
 * The properties of this class are described by the constructor documentation.
 */
export default class ObligationResultHistory {
  private _obligationIdx: number;
  private _last: ObligationResult | undefined;
  private _saved: ObligationResult[];

  /**
   * @param obligationIdx - index of the proof obligation this history contains proofs for.
   *                        Proof obligations are counted from top to bottom in their corresponding
   *                        source file and this index is the count of the obligation.
   * @param last - most recent proof attempt at that obligation
   * @param saved - proofs saved in the history
   */
  constructor(
    obligationIdx: number,
    last: ObligationResult | undefined,
    saved: ObligationResult[]
  ) {
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
