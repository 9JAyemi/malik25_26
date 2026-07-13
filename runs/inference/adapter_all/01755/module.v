module top_module (
   input clk,
   input reset,      // Synchronous active-high reset
   input [7:0] d1,   // 8-bit input for adder 1
   input [7:0] d2,   // 8-bit input for adder 2
   input select,      // Select input to choose between adder 1 and adder 2
   output reg [7:0] q    // 8-bit output from the functional module
);

reg [7:0] q1, q2;
reg cin1, cin2;
wire [7:0] sum1, sum2;
wire cout1, cout2;

adder adder1(
   .a(d1),
   .b(q1),
   .cin(cin1),
   .sum(sum1),
   .cout(cout1)
);

adder adder2(
   .a(d2),
   .b(q2),
   .cin(cin2),
   .sum(sum2),
   .cout(cout2)
);

always @(posedge clk) begin
   if (reset) begin
      q <= 0;
   end else begin
      if (select) begin
         q <= sum1;
      end else begin
         q <= sum2;
      end
   end
end

always @(posedge clk) begin
   if (reset) begin
      q1 <= 0;
      q2 <= 0;
      cin1 <= 0;
      cin2 <= 0;
   end else begin
      if (select) begin
         q1 <= d1;
         cin1 <= 1'b0;
         q2 <= sum1;
         cin2 <= cout1;
      end else begin
         q2 <= d2;
         cin2 <= 1'b0;
         q1 <= sum2;
         cin1 <= cout2;
      end
   end
end

endmodule

module adder (
   input [7:0] a,
   input [7:0] b,
   input cin,
   output [7:0] sum,
   output cout
);
   assign {cout, sum} = a + b + cin;
endmodule