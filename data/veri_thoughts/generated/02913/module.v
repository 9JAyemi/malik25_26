module compressor2 #(parameter width = 1)
   (
    input a,
    input b,
    output s,
    output c
   );
   
   assign {c, s} = a + b;
   
endmodule

module ripple_carry_adder
   (
    input [3:0] a,
    input [3:0] b,
    input cin,
    output [3:0] sum,
    output cout
   );

   wire [3:0] s;
   wire [3:0] c;

   compressor2 #(.width(1)) c1(a[0], b[0], s[0], c[0]);
   compressor2 #(.width(1)) c2(s[0], b[1], s[1], c[1]);
   compressor2 #(.width(1)) c3(s[1], b[2], s[2], c[2]);
   compressor2 #(.width(1)) c4(s[2], b[3], s[3], c[3]);

   assign sum = s;
   assign cout = c[3];

endmodule