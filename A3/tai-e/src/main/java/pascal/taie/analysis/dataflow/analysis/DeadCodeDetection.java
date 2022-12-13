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

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.util.collection.Pair;

import java.util.Comparator;
import java.util.Set;
import java.util.TreeSet;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode
        Set<Stmt> peekedCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        DFS(peekedCode, cfg, cfg.getEntry(), constants);
        peekedCode.add(cfg.getExit());
        
        peekedCode.removeIf(stmt -> {
            if (!stmt.getUses().stream().allMatch(DeadCodeDetection::hasNoSideEffect)) 
                return false;
            if (stmt.getDef().isPresent()) {
                LValue lValue = stmt.getDef().get();
                if (lValue instanceof Var var) {
                    var dead = !liveVars.getOutFact(stmt).contains(var);
                    System.out.println("Dead Assign Check " + 
                            (dead ? "<T>" : "<F>") + stmt);
                    return dead;
                }
            }
            return false;
        });
        
        cfg.getNodes().stream()
                .filter(o -> !peekedCode.contains(o))
                .forEach(deadCode::add);
        return deadCode;
    }
    
    public static String GetId(Stmt stmt) {
        return "[" + stmt.getIndex() + "@L" + stmt.getLineNumber() + "]";     
    }
    
    public void DFS(Set<Stmt> peeked, CFG<Stmt> cfg, Stmt current, 
                    DataflowResult<Stmt, CPFact> constants) {
        peeked.add(current);
        for (Edge<Stmt> edge : cfg.getOutEdgesOf(current)) {
            Stmt target = edge.getTarget();
            if (peeked.contains(target))
                continue;
            // 检查语句是否为条件语句，
            // 如果语句是条件语句，
            //   检查条件检查的变量是否为常量，
            //     如果是，选择固定的方向走，不能走的方向直接跳过
            //     如果不是，照常遍历
            // TODO 检查 Exception?
            if (current instanceof JumpStmt) {
                // 检查 inFact 是否没被赋值
                CPFact inFact = constants.getInFact(current);
                
                if (current instanceof If ifStmt) {
                    ConditionExp condition = ifStmt.getCondition();
                    Value evaluate = ConstantPropagation.evaluate(condition, inFact);
                    if (evaluate.isConstant()) {
                        var isTrue = evaluate.getConstant() == 1;
                        System.out.println("If statement " + GetId(ifStmt) + ifStmt + 
                                (isTrue ? "<T>" : "<F>"));
                        // Question: 如果当前分支的跳转本身就是不需要的代码，那么也得把自己移除
                        // 比如 if 1 < 2 : goto 3，这句话本身也是没用的 dead code
                        if (isTrue && edge.getKind() != Edge.Kind.IF_TRUE)
                            continue;
                        if (!isTrue && edge.getKind() != Edge.Kind.IF_FALSE) {
//                            peeked.remove(current);
                            continue;
                        }
                    }
                } else if (current instanceof SwitchStmt switchStmt) {
                    Var var = switchStmt.getVar();
                    Value value = inFact.get(var);
                    if (value.isConstant()) {
                        int constant = value.getConstant();
                        var targetStmt = switchStmt.getCaseTargets().stream()
                                .filter(kv -> kv.first() == constant).findFirst()
                                .orElse(new Pair<>(0, switchStmt.getDefaultTarget()))
                                .second();
                        System.out.println("Switch statement " +
                                GetId(switchStmt)
                                + constant);
                        if (targetStmt != target) {
                            System.out.println("Ignored");
                            continue;
                        }
                    }
                }
            }
            
            DFS(peeked, cfg, target, constants);
        }
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
