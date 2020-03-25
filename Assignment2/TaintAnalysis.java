package Assignment2;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.TreeSet;

import soot.Body;
import soot.Local;
import soot.Value;
import soot.ValueBox;
import soot.jimple.AssignStmt;
import soot.jimple.IdentityStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.ReturnStmt;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.VirtualInvokeExpr;
import soot.tagkit.LineNumberTag;
import soot.toolkits.graph.DirectedGraph;
import soot.toolkits.graph.UnitGraph;
import soot.toolkits.scalar.ArraySparseSet;
import soot.toolkits.scalar.BackwardFlowAnalysis;
import soot.toolkits.scalar.FlowSet;
import soot.toolkits.scalar.Pair;
import soot.util.Chain;

public class TaintAnalysis extends BackwardFlowAnalysis {

	Body b;
    FlowSet inval, outval;
    Set<Local> inputs;
    Set<Local> parameters;
	public TaintAnalysis(UnitGraph g) {
		super(g);
		b = g.getBody();
		inputs = new HashSet<Local>();
		parameters = new HashSet<Local>();
		
		doAnalysis();
		System.out.println("-------------------------------------------------");
		System.out.println("\nInputs: ");
		for(Local ll:inputs) {
			System.out.print(ll.toString()+" ");
		}
		System.out.println("\nParameters: ");
		for(Local ll:parameters) {
			System.out.print(ll.toString()+" ");
		}
		System.out.println();
	}

	@Override
	protected void flowThrough(Object in, Object unit, Object out) {
        inval = (FlowSet) in;
        outval = (FlowSet) out;
        Stmt u = (Stmt) unit;
        inval.copy(outval);
        System.out.println("\nStmt: " + u.toString()+" ");
        System.out.println("InSet: ");
        Iterator it = inval.iterator();
        while (it.hasNext()) {
            String inv = (String)it.next();
            System.out.print(inv+",");
        }
        System.out.println();
        
        
        //Kill all definitions of the var which is defined      
        if(u instanceof AssignStmt) {
        	AssignStmt assign = (AssignStmt)u;
//        	System.out.println("\nAssignment Left Operand: "+ assign.getLeftOp());
        	boolean flag = false;
        	for(ValueBox box:assign.getUseBoxes()) {
        		if(box.getValue() instanceof Local) {
        			flag = true;
        		}
        	}
        	if(assign.containsInvokeExpr()) {
        		InvokeExpr expr = assign.getInvokeExpr();
        		flag = true;
        		if(expr.toString().contains("java.util.Scanner"))
        		{
        			inputs.add((Local)assign.getLeftOp());        		
        		}
        		if(expr instanceof VirtualInvokeExpr  && expr.getMethod().toString().contains("java.lang.StringBuilder")) {
        			flag = false;
        		}
        	
        	}
        	if(flag==false) {
        		outval.remove(assign.getLeftOp().toString());
        	}
        }
        
        //Gen the new definition: current one
        if(u instanceof ReturnStmt) 
        {
        	ReturnStmt ret = (ReturnStmt)u;
        	for(ValueBox box:ret.getUseBoxes()) 
        	{
        		if(box.getValue() instanceof Local) {
        			if(!(outval.contains(box.getValue().toString()))) {
	        			outval.add(box.getValue().toString());
	        		}
    			}
        	}
        }
        if(u instanceof InvokeStmt) {
        	InvokeStmt invoke = (InvokeStmt)u;
        	if(invoke.getInvokeExpr() instanceof VirtualInvokeExpr) {
        		VirtualInvokeExpr vix = (VirtualInvokeExpr)invoke.getInvokeExpr();
        		if(vix.getMethod().toString().contains("java.io.PrintStream")) {
        			for(Value val: vix.getArgs())
        			{
        				if(val instanceof Local) {
            				if(!(outval.contains(val.toString()))) {
        	        			outval.add(val.toString());
        	        		}
            			}
        			}
        		}
        	}
        }
        if(u instanceof AssignStmt) {
        	AssignStmt assign = (AssignStmt)u;
        	if(inval.contains(assign.getLeftOp().toString()) && !(assign.containsInvokeExpr()))
        	{
        		for(ValueBox box: assign.getUseBoxes()) {
        			if(box.getValue() instanceof Local) {
        				if(!(outval.contains(box.getValue().toString()))) {
    	        			outval.add(box.getValue().toString());
    	        		}
        			}
        		}
        	}
        	if(inval.contains(assign.getLeftOp().toString()) && assign.containsInvokeExpr()) {
        		InvokeExpr expr = (InvokeExpr)assign.getInvokeExpr();
        		for(Value val: expr.getArgs()) {
        			if(val instanceof Local) {
        				if(!(outval.contains(val.toString()))) {
    	        			outval.add(val.toString());
    	        		}
        			}
        		}
        		if(expr instanceof VirtualInvokeExpr  && expr.getMethod().toString().contains("java.lang.StringBuilder")) 
        		{
        			VirtualInvokeExpr vix = (VirtualInvokeExpr)expr;
//        			System.out.println(vix.getBase());
        			outval.add(vix.getBase().toString());
        		}
        	}
        }
        
        
        
        if(u instanceof IdentityStmt) {
        	IdentityStmt ident = (IdentityStmt)u;
        	String var;
        	var = u.toString();
            if ( outval.contains(ident.getLeftOp().toString()) && var.contains("@parameter") ) {
            	parameters.add((Local)ident.getLeftOp());
            }
        }
               
        System.out.println("\nOutset: ");
        Iterator itOut = outval.iterator();
        while (itOut.hasNext()) {
            String inv = (String)itOut.next();
            System.out.print(inv+",");
        }
        System.out.println();
	}

	@Override
	protected void copy(Object source, Object dest) {
		FlowSet srcSet = (FlowSet) source;
        FlowSet destSet = (FlowSet) dest;
        srcSet.copy(destSet);
	}
	@Override
	protected Object entryInitialFlow() {
        ArraySparseSet as = new ArraySparseSet();
        return as;

	}

	@Override
	protected void merge(Object out1, Object out2, Object in) {
		FlowSet inval1 = (FlowSet) out1;
        FlowSet inval2 = (FlowSet) out2;
        FlowSet outVal = (FlowSet) in;
        inval1.union(inval2, outVal); //Merging in may analysis
	}

	@Override
	protected Object newInitialFlow() {
		ArraySparseSet as = new ArraySparseSet();
        return as;
	}

}
