module negate_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic S,
    input logic MO
);

    // No RTL clock/reset; sample combinational behavior on clk.

    // MO always matches the RTL ternary inversion.
    check_output_function: assert property (
        @(posedge clk) MO == ((S == 1'b1) ? ~B : ~A)
    );

    // When S selects B and B is low, MO is high.
    check_select_b_when_b_low: assert property (
        @(posedge clk) ((S == 1'b1) && (B == 1'b0)) |-> (MO == 1'b1)
    );

    // When S selects B and B is high, MO is low.
    check_select_b_when_b_high: assert property (
        @(posedge clk) ((S == 1'b1) && (B == 1'b1)) |-> (MO == 1'b0)
    );

    // When S selects A and A is low, MO is high.
    check_select_a_when_a_low: assert property (
        @(posedge clk) ((S == 1'b0) && (A == 1'b0)) |-> (MO == 1'b1)
    );

    // When S selects A and A is high, MO is low.
    check_select_a_when_a_high: assert property (
        @(posedge clk) ((S == 1'b0) && (A == 1'b1)) |-> (MO == 1'b0)
    );

endmodule