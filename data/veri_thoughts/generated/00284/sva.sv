module sky130_fd_sc_ls__a211oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // Y must match the RTL combinational equation.
    check_y_matches_rtl_equation: assert property (
        @(posedge clk)
        Y == ((A1 & A2) |
              ((!A1) & (!A2) & B1 & (!C1)) |
              ((!A1) & (!A2) & (!B1) & C1))
    );

    // If both A inputs are high, Y must be high.
    check_a_inputs_both_high_set_y: assert property (
        @(posedge clk)
        (A1 && A2) |-> Y
    );

    // If A1 and A2 differ, Y must be low.
    check_a_inputs_mismatch_clear_y: assert property (
        @(posedge clk)
        (A1 ^ A2) |-> !Y
    );

    // If both A inputs are low, Y must equal B1 XOR C1.
    check_a_inputs_both_low_reduce_to_xor: assert property (
        @(posedge clk)
        ((!A1) && (!A2)) |-> (Y == (B1 ^ C1))
    );

endmodule