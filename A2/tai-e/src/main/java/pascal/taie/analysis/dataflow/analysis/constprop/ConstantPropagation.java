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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

import java.util.List;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        // 以最 safe 的情况估测传入的参数
        CPFact cpFact = new CPFact();
        List<Var> params = cfg.getIR().getParams();
        params.forEach(v -> cpFact.update(v, Value.getNAC()));
        return cpFact;
    }

    public CPFact getAllUndefFact(CFG<Stmt> cfg) {
        var fact = new CPFact();
        // find all variable, set UNDEF for them
        for (var node : cfg) {
            for (RValue use : node.getUses()) {
                if (use instanceof Var var) {
                    fact.update(var, Value.getUndef());
                }
            }
            if (node.getDef().isPresent() && node.getDef().get() instanceof Var var) {
                fact.update(var, Value.getUndef());
            }
        }
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        fact.forEach((var, value) -> {
            Value formal = target.get(var);
            var meet = meetValue(value, formal);
            target.update(var, meet);
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value value, Value formal) {
        // TODO - finish me
        if (formal.isUndef()) {
            return value;
        } else if (formal.isNAC()) {
            // keep NAC
            return formal;
        } else if (formal.isConstant()) {
            if (value.isConstant()) {
                if (value.getConstant() != formal.getConstant()) {
                    return Value.getNAC();
                } // else no update
                else {
                    return formal;
                }
            } else if (value.isNAC()) {
                return value;
            }
        }
        // no else, cannot reach here
        throw new UnsupportedOperationException();
//        return null;
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        // no change if not new def
        var oldOut = out.copy();
        meetInto(in, out);
        if (stmt instanceof DefinitionStmt<?, ?> defStmt) {
            RValue rValue = defStmt.getRValue();
            var lValue = (Var) defStmt.getLValue();
            if (lValue != null) {
                var eval = evaluate(rValue, in);
                if (evaluate(rValue, in) != null)
                    out.update(lValue, eval);
            }
        }
        return !oldOut.equals(out);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    public static Value getValue(Var var, CPFact in) {
        if (!canHoldInt(var))
            return Value.getUndef();
        if (var.isTempConst() && var.getTempConstValue() instanceof IntLiteral intLiteral) {
            return Value.makeConstant(intLiteral.getValue());
        }
        return in.get(var);
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        if (exp instanceof IntLiteral intLiteral) {
            return Value.makeConstant(intLiteral.getValue());
        } else if (exp instanceof Var rVar) {
            return getValue(rVar, in);
        } else if (exp instanceof BinaryExp biExp) {
            Value v1 = getValue(biExp.getOperand1(), in);
            Value v2 = getValue(biExp.getOperand2(), in);
            if (v1.isConstant() && v2.isConstant()) {
                var v = evaluateBiExp(biExp, v1.getConstant(), v2.getConstant());
                return Value.makeConstant(v);
            } else if (v1.isNAC() || v2.isNAC()) {
                return Value.getNAC();
            } else {
                return Value.getUndef();
            }
        } else if (exp instanceof InvokeExp) {
            // 同理使用最 safe 最 useless 的情况
            return Value.getNAC();
        }
        // 测试 interprocedure 里面，有一个 InvokeSpecial
        // 不知道其他是什么 Exp 了！全都给我 NAC 吧！
        return Value.getNAC();
    }

    public static int toInt(boolean bool) {
        return bool ? 1 : 0;
    }

    public static int evaluateBiExp(BinaryExp exp, int o1, int o2) {
        if (exp instanceof ArithmeticExp arithmeticExp) {
            switch (arithmeticExp.getOperator()) {
                case ADD -> {
                    return o1 + o2;
                }
                case SUB -> {
                    return o1 - o2;
                }
                case MUL -> {
                    return o1 * o2;
                }
                case DIV -> {
                    return o1 / o2;
                }
                case REM -> {
                    return o1 % o2;
                }
            }
        } else if (exp instanceof BitwiseExp bitwiseExp) {
            switch (bitwiseExp.getOperator()) {
                case OR -> {
                    return o1 | o2;
                }
                case AND -> {
                    return o1 & o2;
                }
                case XOR -> {
                    return o1 ^ o2;
                }
            }
        } else if (exp instanceof ConditionExp conditionExp) {
            switch (conditionExp.getOperator()) {
                case EQ -> {
                    return toInt(o1 == o2);
                }
                case NE -> {
                    return toInt(o1 != o2);
                }
                case LT -> {
                    return toInt(o1 < o2);
                }
                case GT -> {
                    return toInt(o1 > o2);
                }
                case LE -> {
                    return toInt(o1 <= o2);
                }
                case GE -> {
                    return toInt(o1 >= o2);
                }
            }
        } else if (exp instanceof ShiftExp shiftExp) {
            switch (shiftExp.getOperator()) {
                case SHL -> {
                    return o1 << o2;
                }
                case SHR -> {
                    return o1 >> o2;
                }
                case USHR -> {
                    return o1 >>> o2;
                }
            }
        }
        return 0;
    }
}
