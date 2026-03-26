module nor2_gate_sva(
    input logic clk,
    input logic A,
    input logic B_N,
    input logic Y
);

    // Y must equal the NOR of A and B_N.
    check_nor_equation: assert property (
        @(posedge clk) disable iff (1'b0) Y == ~(A | B_N)
    );

    // When both inputs are low, Y must be high.
    check_both_low_drives_high: assert property (
        @(posedge clk) disable iff (1'b0) (!A && !B_N) |-> Y
    );

    // A high must force Y low.
    check_a_high_drives_low: assert property (
        @(posedge clk) disable iff (1'b0) A |-> !Y
    );

    // B_N high must force Y low.
    check_b_high_drives_low: assert property (
        @(posedge clk) disable iff (1'b0) B_N |-> !Y
    );

    // Y high implies both inputs are low.
    check_high_output_requires_both_low: assert property (
        @(posedge clk) disable iff (1'b0) Y |-> (!A && !B_N)
    );

endmodule