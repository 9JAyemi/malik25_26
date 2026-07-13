module and3_gate_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic Y
);

    // Y matches the RTL boolean function.
    check_output_function: assert property (
        @(posedge clk) Y == ((A & B) | (B & C))
    );

    // B low forces Y low.
    check_b_low_forces_y_low: assert property (
        @(posedge clk) (B == 1'b0) |-> (Y == 1'b0)
    );

    // A and B high force Y high.
    check_ab_high_drives_y_high: assert property (
        @(posedge clk) ((A == 1'b1) && (B == 1'b1)) |-> (Y == 1'b1)
    );

    // B and C high force Y high.
    check_bc_high_drives_y_high: assert property (
        @(posedge clk) ((B == 1'b1) && (C == 1'b1)) |-> (Y == 1'b1)
    );

    // A high cannot raise Y when B is low.
    check_a_without_b_keeps_y_low: assert property (
        @(posedge clk) ((A == 1'b1) && (B == 1'b0)) |-> (Y == 1'b0)
    );

    // C high cannot raise Y when B is low.
    check_c_without_b_keeps_y_low: assert property (
        @(posedge clk) ((C == 1'b1) && (B == 1'b0)) |-> (Y == 1'b0)
    );

    // Y high requires B high.
    check_y_high_requires_b_high: assert property (
        @(posedge clk) (Y == 1'b1) |-> (B == 1'b1)
    );

    // Y high requires A or C high.
    check_y_high_requires_a_or_c: assert property (
        @(posedge clk) (Y == 1'b1) |-> ((A == 1'b1) || (C == 1'b1))
    );

endmodule