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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Stmt;

/**
 * Implementation of classic live variable analysis.
 */
public class LiveVariableAnalysis extends
        AbstractDataflowAnalysis<Stmt, SetFact<Var>> {

    public static final String ID = "livevar";

    public LiveVariableAnalysis(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return false;
    }

    @Override
    public SetFact<Var> newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        return new SetFact<>();
    }

    @Override
    public SetFact<Var> newInitialFact() {
        // TODO - finish me
        return new SetFact<>();
    }

    @Override
    public void meetInto(SetFact<Var> fact, SetFact<Var> target) {
        // TODO - finish me
        target.union(fact);
    }

    @Override
    public boolean transferNode(Stmt stmt, SetFact<Var> in, SetFact<Var> out) {
        // TODO - finish me
        // use U (out - def)
        String log = "";
        log += "TRANSFER: " + stmt + "\n";

        SetFact<Var> varSetFact = new SetFact<>();
        var uses = stmt.getUses().stream()
                .filter(use -> use instanceof Var).toList();
        uses.forEach(use -> varSetFact.add((Var)use));

        var old_union = in.copy();

        in.union(out);
        if (stmt.getDef().isPresent()) {
            LValue lValue = stmt.getDef().get();
            if (lValue instanceof Var) {
                // 之前使用了 out.remove，导致对 out 本身的修改，直接导致结果的错误，查了很久
                // 原因是陷入了 IN = use U (out - def) 的运算顺序的临近误区
                // 最后改成了 in = in U out, in = in - def, in = in U use 的执行顺序
                in.remove(((Var) lValue));
                log += "\tremove: " + lValue + ";";
            }
        }

        in.union(varSetFact);

        log += "\tuses: " + uses + "\tresults: " + in;
//        System.out.println(log);
        return !in.equals(old_union);
    }
}
