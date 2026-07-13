module my_or3_assertions (
    input logic clk,
    input logic A,
    input logic B,
    input logic C_N,
    input logic X
);

    // X must equal the OR of A, B, and C_N.
    check_or3_equivalence: assert property (
        @(posedge clk) disable iff (1'b0) X == (A | B | C_N)
    );

    // If all inputs are low, X must be low.
    check_all_low_drives_x_low: assert property (
        @(posedge clk) disable iff (1'b0) (!A && !B && !C_N) |-> !X
    );

    // A high must force X high.
    check_a_high_drives_x_high: assert property (
        @(posedge clk) disable iff (1'b0) A |-> X
    );

    // B high must force X high.
    check_b_high_drives_x_high: assert property (
        @(posedge clk) disable iff (1'b0) B |-> X
    );

    // C_N high must force X high.
    check_cn_high_drives_x_high: assert property (
        @(posedge clk) disable iff (1'b0) C_N |-> X
    );

    // X low implies all inputs are low.
    check_x_low_implies_all_inputs_low: assert property (
        @(posedge clk) disable iff (1'b0) !X |-> (!A && !B && !C_N)
    );

endmodule