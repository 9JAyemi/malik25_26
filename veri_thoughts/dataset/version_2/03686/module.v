
 module lookahead(c_in, c_out, c, p, g, P, G);
   input [3:0] p, g;
   input c_in;
   
   output [2:0] c;
   output c_out;
   output P, G;
   
   assign #2 c[0] = g[0] | (p[0] & c_in); 
   assign #3 c[1] = g[1] | (g[0] & p[1]) | (p[1] & p[0] & c_in); 
   assign #4 c[2] = g[2] | (g[1] & p[2]) | (g[0] & p[1] & p[2]) | (p[2] & p[1] & p[0] & c_in); 
   assign #5 c_out = g[3] | (g[2] & p[3]) | (g[1] & p[2] & p[3]) | (g[0] & p[1] & p[2] & p[3]) | (p[3] & p[2] & p[1] & p[0] & c_in);  
   
   assign #4 G = g[3] | (g[2] & p[3]) | (g[1] & p[2] & p[3]) | (p[3] & p[2] & p[1] & g[0]);
   assign #3 P = p[3] & p[2] & p[1] & p[0];
   
endmodule
