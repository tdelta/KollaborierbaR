import Displaynode from './displaynode.ts';
import ProofResult from '../../../key/netdata/ProofResults';

export default class Displaytree {

    private addNode: (node:Displaynode) => void;
    private setCollapseFromDisplay: (path: ProofResult[]) => void;

}