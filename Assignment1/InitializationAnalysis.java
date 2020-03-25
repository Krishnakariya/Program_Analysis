package LabAssignment1;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import soot.Body;
import soot.Local;
import soot.ValueBox;
import soot.jimple.AssignStmt;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.Stmt;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.UnitGraph;
import soot.toolkits.scalar.ArraySparseSet;
import soot.toolkits.scalar.FlowSet;
import soot.toolkits.scalar.ForwardFlowAnalysis;
import soot.util.Chain;

public class InitializationAnalysis extends ForwardFlowAnalysis {

	Body b;
	FlowSet inval, outval;
	Set<String> ans;
	public InitializationAnalysis(UnitGraph g)
	{
		super(g);
		b = g.getBody();
		ans = new HashSet<String>();
		doAnalysis();
		for (Iterator iterator = ans.iterator(); iterator.hasNext();) {
			String string = (String) iterator.next();
			System.out.println(string);
		}
	}
	@Override
	protected void flowThrough(Object in, Object unit, Object out) {
		inval = (FlowSet)in;
		outval = (FlowSet)out;
		Stmt u = (Stmt)unit;
//		System.out.println(u);
//		System.out.println();
		inval.copy(outval);
		// Kill operation
		if(u instanceof AssignStmt) {
//			System.out.println(u.toString());
			Iterator<ValueBox> defIt = u.getDefBoxes().iterator();
			while(defIt.hasNext())
			{
				ValueBox defBox = (ValueBox)defIt.next();

				if (defBox.getValue() instanceof Local) {
					Iterator inIt = inval.iterator();
					while (inIt.hasNext()) {
						Tuple t = (Tuple)inIt.next();
//						System.out.println(t + " "+defBox.getValue()+" "+t.flag);
						if(t.x.getName().equals( ((Local)defBox.getValue()).toString() ) && t.flag==0) {
							outval.remove(t);
//							System.out.println("Removed : "+t);
							Tuple t2 = new Tuple(t.x,u.toString(),1);
							outval.add(t2);
							ans.add(u.toString());
//							System.out.println(u.toString());
						}
					}
				}
			}
//			System.out.println();
//			Iterator outIt = outval.iterator();
		}		
		if(u instanceof ReturnVoidStmt || u instanceof ReturnStmt) {
			Iterator inIt = inval.iterator();
			while (inIt.hasNext()) {
				Tuple t = (Tuple)inIt.next();
//				System.out.println(t.x.toString());
				if(!(t.x.toString().equals("this")) && t.flag == 0) {
					
					ans.add(t.toString());
				}
			}
		}
		//Gen operation
//		if (u instanceof AssignStmt)
//			outval.add(new Tuple((Local)u.getDefBoxes().get(0).getValue(),"?",0));
		
//		if (u instanceof AssignStmt)
//		{
//			System.out.println("In: " + inval);
//			System.out.println("Unit: " + u.toString());
//			System.out.println("Out :" + outval);
//			System.out.println();
//		}
		
	}
	@Override
	protected void copy(Object source, Object dest) {
		FlowSet srcSet = (FlowSet)source;
		FlowSet	destSet = (FlowSet)dest;
//		for (Iterator iterator = srcSet.iterator(); iterator.hasNext();) {
//			Tuple t = (Tuple)iterator;
//			destSet.add(new Tuple(t.x,t.value,t.flag));
//		}
		srcSet.copy(destSet);
	}
	@Override
	protected Object entryInitialFlow() {
		ArraySparseSet arr = new ArraySparseSet();
		Chain<Local> c = b.getLocals();
		for (Iterator iterator = c.iterator(); iterator.hasNext();) {
			Local local = (Local) iterator.next();
			arr.add(new Tuple(local, "?", 0));
		}
		return arr;
	}
	@Override
	protected void merge(Object in1, Object in2, Object out) {
		FlowSet inval1=(FlowSet)in1;
		FlowSet inval2=(FlowSet)in2;
		FlowSet outSet=(FlowSet)out;
		// May analysis
		inval1.union(inval2, outSet);
//		System.out.println("In merge");
//		System.out.println("inval1:"+inval1);
//		System.out.println("inval2:"+inval2);
//		System.out.println("Outval:"+outval);
//		System.out.println();
		
	}
	@Override
	protected Object newInitialFlow() {
		return new ArraySparseSet();
	}

}
 

class Tuple{
	Local x;
	String value;
	int flag = 0;
	public Tuple(Local v,String s,int f) {
		x = v;
		value = s;
		flag = f;
	}
	@Override
	public String toString() {
		return x.toString() + " " + value;
	}
	@Override
	public boolean equals(Object obj) {
		return this.toString().equals(obj.toString());
	}
	@Override
	protected Object clone() throws CloneNotSupportedException {
		Tuple t = new Tuple(this.x,this.value,this.flag);
		return t;
	}
}