package Assignment2;

import java.util.Scanner;

public class Tester {
	int bar1(int x) {
		int product, a;
		a = 10;
		product = x * a;
		return product;
	}
	static int foo()
	{
	Scanner sc = new Scanner(System.in);

	int z;
	int a = sc.nextInt();
	int b = sc.nextInt();
	int c = 10;
	z = a+b+c;
	return z;
	}
}
//	
//		static int foo(int z) {
//		int a;
//		int b;
//		//{z, a, b}
//		int c = 11;
//		//{z, a, b, c}
//		int d = 5;
//		//{z, a, b, c, d}
//		System.out.println(z);
//		//{z, a, b, c, d}
//		a = z * d;
//		//{z, a, b, c}
//		b = z + c;
//		//{z, a, b}
//		z = a + b;
//		//{z}
//		return z;
//		//{ }
//		}
//		public static void main(String [] args) {
//		//{val}
//		int val = foo(5);
//		//{val}
//		System.out.println(val);
//		//{ }
//		}
//		}
//		/*Sinks depend on parameter (source):
//		foo:- {z}
//		main:- {}*/

	
	
	
//	static int foo(int z)
//	{
//	//{z}
//	int x = 22;
//	//{x, z}
//	int y = 12;
//	//{x, y, z}
//	if(x<10)
//
//	{
//	while(x<20)
//	{
//	//{x, y, z}
//	x = x + z;
//	//{x, y}
//	x++;
//	//{x, y}
//	}
//	}
//	else
//	{
//	while(x<10)
//	{
//	//{x, y}
//	y++;
//	//{x, y}
//	}
//	}
//	//{x, y}
//	System.out.println(x + " " + y);
//	//{x}
//	return x;
//	//{ }
//	}
//	public static void main(String [] args) {
//	//{val}
//	int val = foo(5);
//	//{val}
//	System.out.println(val);
//	//{ }
//	}
//}