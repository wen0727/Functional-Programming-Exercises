// Polynomial.dll must be referenced
using System;
using Microsoft.FSharp.Collections; // where the type FSharpList<T> is found
namespace ConsoleApp1
{
    class Program
    {
        static void Main(string[] args)
        { 
            int[] n1 = new int[] {1, 0, -3 };
            FSharpList<int> n3; // FSharp.Core must referenced
            Polynomial.Poly p1 = Polynomial.ofArray(n1);
            Polynomial.Poly p2 = Polynomial.ofArray(new int[] { 0, 0, -2});
            Polynomial.Poly p3 = p1 + p2 * p1;
            Polynomial.Poly p4 = p3 - p3;
            Polynomial.Degree d3 = Polynomial.degree(p3);
            Polynomial.Degree d4 = Polynomial.degree(p4);
            Console.WriteLine("p1(x) is " + p1);
            Console.WriteLine("p2(x) is " + p2);
            Console.WriteLine("p3(x) is " + p3);
            Console.WriteLine("p4(x) is " + p4);
            Console.WriteLine("Degree of p3(x) is " + d3);
            Console.WriteLine("Degree of p4(x) is " + d4);
            n3 = Polynomial.toList(p3);
            Console.Write("Coefficients of p3(x) are ");
            foreach (int n in n3)
            Console.Write(n + " ");
            Console.WriteLine("");
            Console.WriteLine("p3'(x) is " + Polynomial.derivative(p3));
            n3 = Polynomial.toList(Polynomial.compose(p1, p2));
            Console.Write("Coefficients of p1(p2(x)) are ");
            foreach (int n in n3)
            Console.Write(n + " ");
            Console.WriteLine("");
            Console.ReadKey();
        }
    }
}