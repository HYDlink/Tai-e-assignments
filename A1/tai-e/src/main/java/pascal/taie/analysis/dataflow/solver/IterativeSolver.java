/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Stmt;

import java.util.Collections;

class IterativeSolver<Node, Fact> extends Solver<Node, Fact> {

    public IterativeSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        throw new UnsupportedOperationException();
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        boolean changed = true;
        int iterate_times = 0;
        var iterate_nodes = new java.util.ArrayList<>(cfg.getNodes().stream().toList());
        Collections.reverse(iterate_nodes);
        while (changed) {
            changed = false;
            System.out.printf("iterate times: %d\n", iterate_times);
            iterate_times++;
            for (Node node : iterate_nodes) {
                var stmt = (Stmt)node;

                // union all input
                var target = analysis.newInitialFact();
                assert target != null;
                for (var nodeEdge : cfg.getOutEdgesOf(node)) {
                    Node out = nodeEdge.getTarget();
                    Fact inFact = result.getInFact(out);
                    analysis.meetInto(inFact, target);
                }
                result.setOutFact(node, target);

                var inFact = result.getInFact(node);

                // Transfer function
                if (analysis.transferNode(node, inFact, target))
                    changed = true;

                result.setInFact(node, inFact);
            }
        }
    }
}
