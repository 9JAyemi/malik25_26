module and_gate_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic VPWR,
    input logic X,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // X must equal the AND of A1, A2, B1, and VPWR.
    check_x_matches_and: assert property (
        @(posedge clk) X == (A1 & A2 & B1 & VPWR)
    );

    // When all functional inputs are high, X must be high.
    check_x_high_when_all_inputs_high: assert property (
        @(posedge clk) (A1 && A2 && B1 && VPWR) |-> X
    );

    // If any functional input is low, X must be low.
    check_x_low_when_any_input_low: assert property (
        @(posedge clk) ((!A1) || (!A2) || (!B1) || (!VPWR)) |-> !X
    );

    // A high X implies all functional inputs are high.
    check_x_implies_all_inputs_high: assert property (
        @(posedge clk) X |-> (A1 && A2 && B1 && VPWR)
    );

endmodule