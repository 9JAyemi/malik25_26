module sky130_fd_sc_ms__nor3b_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C_N,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // Y must match the RTL NOR equation of A, B, and C_N.
    check_nor3b_equation: assert property (
        @(posedge clk) disable iff (1'b0) Y == ~(A | B | C_N)
    );

    // If all functional inputs are low, Y must be high.
    check_all_inputs_low_sets_y_high: assert property (
        @(posedge clk) disable iff (1'b0) !(A | B | C_N) |-> Y
    );

    // If any functional input is high, Y must be low.
    check_any_input_high_sets_y_low: assert property (
        @(posedge clk) disable iff (1'b0) (A | B | C_N) |-> !Y
    );

    // If the functional inputs stay the same, Y must stay the same.
    check_stable_inputs_keep_output_stable: assert property (
        @(posedge clk) disable iff (1'b0) ($stable(A) && $stable(B) && $stable(C_N)) |-> $stable(Y)
    );

endmodule