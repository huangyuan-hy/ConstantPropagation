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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private boolean enableTaintAnalysis;

    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    public AnalysisOptions getOptions() {
        return options;
    }

    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    public CSManager getCSManager() {
        return csManager;
    }

    public void addVarPointsTo(Pointer pointer, PointsToSet pointsToSet) {
        workList.addEntry(pointer, pointsToSet);
    }

    void solve() {
        initialize();
        analyze();
        if (enableTaintAnalysis) {
            taintAnalysis.onFinish();
        }
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        enableTaintAnalysis = options.getString("taint-config") != null;
        if (enableTaintAnalysis) {
            taintAnalysis = new TaintAnalysiss(this);
        }
       
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }


    private void addReachable(CSMethod csMethod) {
        if (callGraph.addReachableMethod(csMethod)) {
            JMethod method = csMethod.getMethod();
            StmtProcessor stmtProcessor = new StmtProcessor(csMethod);
            method.getIR().forEach(s -> s.accept(stmtProcessor));
        }
    }


    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        @Override
        public Void visit(New stmt) {

            CSVar v = csManager.getCSVar(context, stmt.getLValue());
            Obj obj = heapModel.getObj(stmt);
            Context heapContext = contextSelector.selectHeapContext(csMethod, obj);
            CSObj csObj = csManager.getCSObj(heapContext, obj);
            workList.addEntry(v, PointsToSetFactory.make(csObj));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            CSVar from = csManager.getCSVar(context, stmt.getRValue());
            CSVar to = csManager.getCSVar(context, stmt.getLValue());
            addPFGEdge(from, to);
            return null;
        }


        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                JField field = stmt.getFieldRef().resolve();
                StaticField sfield = csManager.getStaticField(field);
                CSVar to = csManager.getCSVar(context, stmt.getLValue());
                addPFGEdge(sfield, to);
            }
            return null;
        }


        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                JField field = stmt.getFieldRef().resolve();
                StaticField sfield = csManager.getStaticField(field);
                CSVar from = csManager.getCSVar(context, stmt.getRValue());
                addPFGEdge(from, sfield);
            }
            return null;
        }


        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                JMethod callee = resolveCallee(null, stmt);
                CSCallSite csCallSite = csManager.getCSCallSite(context, stmt);
                Context calleeCtx = contextSelector.selectContext(csCallSite, callee);
                CSMethod csCallee = csManager.getCSMethod(calleeCtx, callee);
                processCallEdge(new Edge<>(CallKind.STATIC, csCallSite, csCallee));
            }
            return null;
        }
    }


    private void addPFGEdge(Pointer source, Pointer target) {
        if (pointerFlowGraph.addEdge(source, target)) {
            if (!source.getPointsToSet().isEmpty()) {
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }


    private void analyze() {
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer p = entry.pointer();
            PointsToSet pts = entry.pointsToSet();
            PointsToSet diff = propagate(p, pts);
            if (p instanceof CSVar v) {
                if (enableTaintAnalysis) {
                    taintAnalysis.onNewPointsToSet(v, diff);
                }
                for (CSObj o : diff) {
                    processInstanceStore(v, o);
                    processInstanceLoad(v, o);
                    processArrayStore(v, o);
                    processArrayLoad(v, o);
                    processCall(v, o);
                }
            }
        }
    }


    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        logger.trace("Propagate {} to {}", pointsToSet, pointer);
        final PointsToSet diff = PointsToSetFactory.make();
        pointsToSet.forEach(obj -> {
            if (pointer.getPointsToSet().addObject(obj)) {
                diff.addObject(obj);
            }
        });
        if (!diff.isEmpty()) {
            pointerFlowGraph.getSuccsOf(pointer)
                    .forEach(succ -> workList.addEntry(succ, diff));
        }
        return diff;
    }


    private void processInstanceStore(CSVar baseVar, CSObj baseObj) {
        Context context = baseVar.getContext();
        Var var = baseVar.getVar();
        for (StoreField store : var.getStoreFields()) {
            Var fromVar = store.getRValue();
            CSVar from = csManager.getCSVar(context, fromVar);
            InstanceField instField = csManager.getInstanceField(
                    baseObj, store.getFieldRef().resolve());
            addPFGEdge(from, instField);
        }
    }


    private void processInstanceLoad(CSVar baseVar, CSObj baseObj) {
        Context context = baseVar.getContext();
        Var var = baseVar.getVar();
        for (LoadField load : var.getLoadFields()) {
            Var toVar = load.getLValue();
            CSVar to = csManager.getCSVar(context, toVar);
            InstanceField instField = csManager.getInstanceField(
                    baseObj, load.getFieldRef().resolve());
            addPFGEdge(instField, to);
        }
    }


    private void processArrayStore(CSVar arrayVar, CSObj array) {
        Context context = arrayVar.getContext();
        Var var = arrayVar.getVar();
        for (StoreArray store : var.getStoreArrays()) {
            Var rvalue = store.getRValue();
            CSVar from = csManager.getCSVar(context, rvalue);
            ArrayIndex arrayIndex = csManager.getArrayIndex(array);
            addPFGEdge(from, arrayIndex);
        }
    }


    private void processArrayLoad(CSVar arrayVar, CSObj array) {
        Context context = arrayVar.getContext();
        Var var = arrayVar.getVar();
        for (LoadArray load : var.getLoadArrays()) {
            Var lvalue = load.getLValue();
            CSVar to = csManager.getCSVar(context, lvalue);
            ArrayIndex arrayIndex = csManager.getArrayIndex(array);
            addPFGEdge(arrayIndex, to);
        }
    }


    private void processCall(CSVar recv, CSObj recvObj) {
        Context context = recv.getContext();
        Var var = recv.getVar();
        for (Invoke callSite : var.getInvokes()) {

            JMethod callee = resolveCallee(recvObj, callSite);

            CSCallSite csCallSite = csManager.getCSCallSite(context, callSite);
            Context calleeContext = contextSelector.selectContext(
                    csCallSite, recvObj, callee);

            CSVar thisVar = csManager.getCSVar(
                    calleeContext, callee.getIR().getThis());
            workList.addEntry(thisVar, PointsToSetFactory.make(recvObj));

            CSMethod csCallee = csManager.getCSMethod(calleeContext, callee);
            processCallEdge(new Edge<>(CallGraphs.getCallKind(callSite),
                    csCallSite, csCallee));
        }
    }

    private void processCallEdge(Edge<CSCallSite, CSMethod> edge) {
        if (callGraph.addEdge(edge)) {
            CSMethod csCallee = edge.getCallee();
            addReachable(csCallee);

            Context callerCtx = edge.getCallSite().getContext();
            Invoke callSite = edge.getCallSite().getCallSite();
            Context calleeCtx = csCallee.getContext();
            JMethod callee = csCallee.getMethod();
            InvokeExp invokeExp = callSite.getInvokeExp();

            for (int i = 0; i < invokeExp.getArgCount(); ++i) {
                Var arg = invokeExp.getArg(i);
                Var param = callee.getIR().getParam(i);
                CSVar argVar = csManager.getCSVar(callerCtx, arg);
                CSVar paramVar = csManager.getCSVar(calleeCtx, param);
                addPFGEdge(argVar, paramVar);
            }

            Var lhs = callSite.getResult();
            if (lhs != null) {
                CSVar csLHS = csManager.getCSVar(callerCtx, lhs);
                for (Var ret : callee.getIR().getReturnVars()) {
                    CSVar csRet = csManager.getCSVar(calleeCtx, ret);
                    addPFGEdge(csRet, csLHS);
                }
            }
            if (enableTaintAnalysis) {
                taintAnalysis.onNewCallEdge(edge);
            }
        }
    }


    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
