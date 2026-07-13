module sky130_fd_sc_hvl__a22oi_assertions (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);

    // Y matches the implemented nand-and-buf logic.
    check_y_gate_equation: assert property (
        @(posedge clk) disable iff (1'b0)
        Y == ((~(A1 & A2)) & (~(B1 & B2)))
    );

    // A1 and A2 high force Y low.
    check_a_pair_forces_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (A1 & A2) |-> (Y == 1'b0)
    );

    // B1 and B2 high force Y low.
    check_b_pair_forces_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (B1 & B2) |-> (Y == 1'b0)
    );

    // If neither input pair is fully high, Y must be high.
    check_no_pair_drives_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (!(A1 & A2) && !(B1 & B2)) |-> (Y == 1'b1)
    );

endmodule