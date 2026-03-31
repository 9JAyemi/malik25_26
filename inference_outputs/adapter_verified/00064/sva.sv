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

// X equals the AND of A1, A2, B1, and VPWR.
    check_x_matches_and_function: assert property (
        @(posedge clk) X == (A1 & A2 & B1 & VPWR)
    );

// If any input is 0, X must be 0.
    check_zero_when_any_input_zero: assert property (
        @(posedge clk) (!A1 || !A2 || !B1 || !VPWR) |-> (X == 1'b0)
    );

// If all inputs are 1, X must be 1.
    check_one_when_all_inputs_one: assert property (
        @(posedge clk) (A1 && A2 && B1 && VPWR) |-> (X == 1'b1)
    );

// A high X requires all inputs to be high.
    check_x_high_requires_all_inputs_high: assert property (
        @(posedge clk) X |-> (A1 && A2 && B1 && VPWR)
    );

// A low X implies at least one input is low.
    check_x_low_requires_some_input_low: assert property (
        @(posedge clk) !X |-> (!A1 || !A2 || !B1 || !VPWR)
    );

endmodule
