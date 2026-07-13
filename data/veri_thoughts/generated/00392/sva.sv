module sky130_fd_sc_hd__nor4b_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D_N
);

    // Y matches the NOR of A, B, C, and the inverted D_N input.
    check_nor4b_function: assert property (
        @(posedge clk) (Y === ~(A | B | C | ~D_N))
    );

    // Y is high when A, B, and C are low and D_N is high.
    check_output_high_condition: assert property (
        @(posedge clk)
        ((A === 1'b0) && (B === 1'b0) && (C === 1'b0) && (D_N === 1'b1)) |-> (Y === 1'b1)
    );

    // Y can only be high when A, B, and C are low and D_N is high.
    check_output_high_only_when_enabled: assert property (
        @(posedge clk)
        (Y === 1'b1) |-> ((A === 1'b0) && (B === 1'b0) && (C === 1'b0) && (D_N === 1'b1))
    );

    // A high forces the NOR output low.
    check_a_high_forces_low: assert property (
        @(posedge clk) (A === 1'b1) |-> (Y === 1'b0)
    );

    // B high forces the NOR output low.
    check_b_high_forces_low: assert property (
        @(posedge clk) (B === 1'b1) |-> (Y === 1'b0)
    );

    // C high forces the NOR output low.
    check_c_high_forces_low: assert property (
        @(posedge clk) (C === 1'b1) |-> (Y === 1'b0)
    );

    // D_N low is inverted internally and forces the NOR output low.
    check_dn_low_forces_low: assert property (
        @(posedge clk) (D_N === 1'b0) |-> (Y === 1'b0)
    );

endmodule