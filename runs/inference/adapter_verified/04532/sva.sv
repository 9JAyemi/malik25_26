module sky130_fd_sc_ms__a21o_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic X,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);

// X matches the RTL combinational equation.
    check_function_equivalence: assert property (
        @(posedge clk) X == ((~(A1 & A2)) & (A1 ^ B1)) | ((~B1) & A1)
    );

// When both A inputs are high, X must be low.
    check_both_a_high_forces_x_low: assert property (
        @(posedge clk) (A1 && A2) |-> !X
    );

// When A1 and B1 differ, X must be high.
    check_a1_xor_b1_forces_x_high: assert property (
        @(posedge clk) (A1 ^ B1) |-> X
    );

// When B1 is low, X must be high.
    check_b1_low_forces_x_high: assert property (
        @(posedge clk) !B1 |-> X
    );

// When A1 is low, X must be low.
    check_a1_low_forces_x_low: assert property (
        @(posedge clk) !A1 |-> !X
    );

// A high X requires either A1 and B1 to differ or B1 to be low.
    check_x_high_has_valid_cause: assert property (
        @(posedge clk) X |-> ((A1 ^ B1) || !B1)
    );

// A low X requires both A inputs to be high.
    check_x_low_has_valid_cause: assert property (
        @(posedge clk) !X |-> (A1 && A2)
    );

endmodule
