import ObligationResult, {
  ObligationResultKind,
} from './netdata/ObligationResult';

export default class ObligationResultHistory {
  private _obligationIdx: number;
  private _last: ObligationResult | undefined;
  private _saved: ObligationResult[];

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
