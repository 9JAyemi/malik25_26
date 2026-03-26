module UAdder (out,carry_out,overflow,A,B,C_in);
   output [31:0]out;
   output      carry_out,overflow;
   input [31:0] A,B;
   input       C_in;
   wire [6:0]  carry;
   
   CLA_4bit cc1(out[3:0],carry[0],A[3:0],B[3:0],C_in);
   CLA_4bit cc2(out[7:4],carry[1],A[7:4],B[7:4],carry[0]);
   CLA_4bit cc3(out[11:8],carry[2],A[11:8],B[11:8],carry[1]);
   CLA_4bit cc4(out[15:12],carry[3],A[15:12],B[15:12],carry[2]);
   CLA_4bit cc5(out[19:16],carry[4],A[19:16],B[19:16],carry[3]);
   CLA_4bit cc6(out[23:20],carry[5],A[23:20],B[23:20],carry[4]);
   CLA_4bit cc7(out[27:24],carry[6],A[27:24],B[27:24],carry[5]);
   CLA_4bito cc8(out[31:28],carry_out,overflow,A[31:28],B[31:28],carry[6]);
endmodule

module CLA_4bit(out,carry_out,A,B,C_in);
   output [3:0]out;
   output      carry_out;
   input [3:0] A,B;
   input       C_in;
   wire  [3:0] p,g;
   wire [9:0] andl1;
   wire [3:0] carry ;
   
   xor xx1(p[0],A[0],B[0]);
   xor xx2(p[1],A[1],B[1]);
   xor xx3(p[2],A[2],B[2]);
   xor xx4(p[3],A[3],B[3]);
   
   and aa1(g[0],A[0],B[0]);
   and aa2(g[1],A[1],B[1]);
   and aa3(g[2],A[2],B[2]);
   and aa4(g[3],A[3],B[3]);

   and al1(andl1[0],p[0],C_in);
   and al2(andl1[1],p[1],g[0]);
   and al3(andl1[2],p[1],p[0],C_in);
   and al4(andl1[3],p[2],g[1]);
   and al5(andl1[4],p[2],p[1],g[0]);
   and al6(andl1[5],p[2],p[1],p[0],C_in);
   and al7(andl1[6],p[3],g[2]);
   and al8(andl1[7],p[3],p[2],g[1]);
   and al9(andl1[8],p[3],p[2],p[1],g[0]);
   and al10(andl1[9],p[3],p[2],p[1],p[0],C_in);

   or oo1(carry[0],g[0],andl1[0]);
   or oo2(carry[1],g[1],andl1[1],andl1[2]);
   or oo3(carry[2],g[2],andl1[3],andl1[4],andl1[5]);
   or oo4(carry_out,g[3],andl1[6],andl1[7],andl1[8],andl1[9]);

   xor xs1(out[0],p[0],C_in);
   xor xs2(out[1],p[1],carry[0]);
   xor xs3(out[2],p[2],carry[1]);
   xor xs4(out[3],p[3],carry[2]);   
endmodule

module CLA_4bito(out,carry_out,overflow,A,B,C_in);
   output [3:0]out;
   output      carry_out,overflow;
   input [3:0] A,B;
   input       C_in;
   wire  [3:0] p,g;
   wire [9:0] andl1;
   wire [2:0] carry ;
   
   xor xx1(p[0],A[0],B[0]);
   xor xx2(p[1],A[1],B[1]);
   xor xx3(p[2],A[2],B[2]);
   xor xx4(p[3],A[3],B[3]);
   
   and aa1(g[0],A[0],B[0]);
   and aa2(g[1],A[1],B[1]);
   and aa3(g[2],A[2],B[2]);
   and aa4(g[3],A[3],B[3]);

   and al1(andl1[0],p[0],C_in);
   and al2(andl1[1],p[1],g[0]);
   and al3(andl1[2],p[1],p[0],C_in);
   and al4(andl1[3],p[2],g[1]);
   and al5(andl1[4],p[2],p[1],g[0]);
   and al6(andl1[5],p[2],p[1],p[0],C_in);
   and al7(andl1[6],p[3],g[2]);
   and al8(andl1[7],p[3],p[2],g[1]);
   and al9(andl1[8],p[3],p[2],p[1],g[0]);
   and al10(andl1[9],p[3],p[2],p[1],p[0],C_in);

   or oo1(carry[0],g[0],andl1[0]);
   or oo2(carry[1],g[1],andl1[1],andl1[2]);
   or oo3(carry[2],g[2],andl1[3],andl1[4],andl1[5]);
   or oo4(carry_out,g[3],andl1[6],andl1[7],andl1[8],andl1[9]);

   xor xs1(out[0],p[0],C_in);
   xor xs2(out[1],p[1],carry[0]);
   xor xs3(out[2],p[2],carry[1]);
   xor xs4(out[3],p[3],carry[2]);
   assign overflow=carry_out^carry[2];
   
endmodule


