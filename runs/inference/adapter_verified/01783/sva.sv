module two_bit_adder_sva (
    input logic clk,
    input logic X,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2,
    input logic OUT
);

// No reset in RTL; sample combinational behavior on clk.

    // OUT equals X1 & X2 (NANDs of inputs).
    check_out_matches_function: assert property (
        @(posedge clk) OUT == ((~A1_N & ~A2_N) & (B1 & B2))
    );

// OUT high implies X is high.
    check_out_high_implies_x_high: assert property (
        @(posedge clk) OUT |-> X
    );

// X high implies OUT high.
    check_x_high_implies_out_high: assert property (
        @(posedge clk) X |-> OUT
    );

// A1_N low forces OUT low.
    check_a1n_low_forces_out_low: assert property (
        @(posedge clk) !A1_N |-> !OUT
    );

// A2_N low forces OUT low.
    check_a2n_low_forces_out_low: assert property (
        @(posedge clk) !A2_N |-> !OUT
    );

// B1 low forces OUT low.
    check_b1_low_forces_out_low: assert property (
        @(posedge clk) !B1 |-> !OUT
    );

// B2 low forces OUT low.
    check_b2_low_forces_out_low: assert property (
        @(posedge clk) !B2 |-> !OUT
    );

// All inputs high drive OUT high.
    check_all_inputs_high_drive_out_high: assert property (
        @(posedge clk) (A1_N & A2_N & B1 & B2) |-> OUT
    );

endmodule
