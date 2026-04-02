module top_module_sva (
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

    // Ensure that q is updated only when select changes
    select_update: assert property (
        @(posedge clk) disable iff (!reset) $changed(select) |-> (q == (select ? sum1 : sum2))
    );

    // Ensure that q1 and q2 are updated correctly based on select
    q1_update: assert property (
        @(posedge clk) disable iff (!reset) $changed(select) |-> (q1 == (select ? d1 : sum2))
    );

    // Ensure that q2 and q1 are updated correctly based on select
    q2_update: assert property (
        @(posedge clk) disable iff (!reset) $changed(select) |-> (q2 == (select ? sum1 : d2))
    );

    // Ensure that cin1 and cin2 are updated correctly based on select
    cin1_update: assert property (
        @(posedge clk) disable iff (!reset) $changed(select) |-> (cin1 == (select ? 1'b0 : cout1))
    );

    // Ensure that cin2 and cin1 are updated correctly based on select
    cin2_update: assert property (
        @(posedge clk) disable iff (!reset) $changed(select) |-> (cin2 == (select ? 1'b0 : cout2))
    );

    // Ensure that q is reset to 0 on reset
    q_reset: assert property (
        @(posedge clk) disable iff (!reset) reset |-> (q == 0)
    );

    // Ensure that q1 is reset to 0 on reset
    q1_reset: assert property (
        @(posedge clk) disable iff (!reset) reset |-> (q1 == 0)
    );

    // Ensure that q2 is reset to 0 on reset
    q2_reset: assert property (
        @(posedge clk) disable iff (!reset) reset |-> (q2 == 0)
    );

    // Ensure that cin1 is reset to 0 on reset
    cin1_reset: assert property (
        @(posedge clk) disable iff (!reset) reset |-> (cin1 == 0)
    );

    // Ensure that cin2 is reset to 0 on reset
    cin2_reset: assert property (
        @(posedge clk) disable iff (!reset) reset |-> (cin2 == 0)
    );

endmodule