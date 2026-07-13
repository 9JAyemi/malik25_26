
module autoinst_multitemplate (
    input Boo1,
    input Boo2,
    input Boo3,
    input b,
    input c,
    output reg [3:0] f4_dotnamed
);

   

   

   wire [1:0] suba1__f2_dotnamed;			 // Templated
   wire [2:0] suba2__f3_dotnamed;
   wire [0:0] suba3__f1_dotnamed;

   SubA #(3,2) suba1 (.a({2'b0,Boo1}), .f2_dotnamed(suba1__f2_dotnamed));
   SubB #(3,3,3) suba2 (.a({2'b0,Boo2}), .b({2'b0,b}), .f3_dotnamed(suba2__f3_dotnamed));
   SubC #(3,3,1) suba3 (.a({2'b0,Boo3}), .c({2'b0,c}), .f1_dotnamed(suba3__f1_dotnamed));

   always @(*) begin
      f4_dotnamed = suba1__f2_dotnamed + suba2__f3_dotnamed + suba3__f1_dotnamed;
   end

endmodule
module SubA #(
    parameter a_width = 3,
    parameter f2_width = 2 // Width of f2_dotnamed
) (
    input [a_width-1:0] a,
    output reg [f2_width-1:0] f2_dotnamed
);

   

   

   always @(*) begin : assign_f2_dotnamed
      f2_dotnamed = a[f2_width-1:0];
   end

endmodule
module SubB #(
    parameter a_width = 3,
    parameter b_width = 3,
    parameter f3_width = 3 // Width of f3_dotnamed
) (
    input [a_width-1:0] a,
    input [b_width-1:0] b,
    output reg [f3_width-1:0] f3_dotnamed
);

   

   

   always @(*) begin : assign_f3_dotnamed
      f3_dotnamed = a[f3_width-1:0] + b[f3_width-1:0];
   end

endmodule
module SubC #(
    parameter a_width = 3,
    parameter c_width = 3,
    parameter f1_width = 1 // Width of f1_dotnamed
) (
    input [a_width-1:0] a,
    input [c_width-1:0] c,
    output reg [f1_width-1:0] f1_dotnamed
);

   

   

   always @(*) begin : assign_f1_dotnamed
      f1_dotnamed = a[f1_width-1:0] & c[f1_width-1:0];
   end

endmodule