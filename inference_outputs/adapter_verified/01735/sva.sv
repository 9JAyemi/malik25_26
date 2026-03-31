module tri_buf_sva (
    input logic clk,
    input logic A,
    input logic Z,
    input logic TE_B
);

// When TE_B is low, Z must be driven to 0.
    check_z_low_when_te_b_low: assert property (
        @(posedge clk) !TE_B |-> (Z == 1'b0)
    );

// When TE_B is high, Z must follow A.
    check_z_follows_a_when_te_b_high: assert property (
        @(posedge clk) TE_B |-> (Z == A)
    );

// A low on Z implies TE_B is low.
    check_te_b_low_when_z_low: assert property (
        @(posedge clk) (Z == 1'b0) |-> !TE_B
    );

// A high on Z implies TE_B is high.
    check_te_b_high_when_z_high: assert property (
        @(posedge clk) (Z == 1'b1) |-> TE_B
    );

// A high on TE_B must drive Z low.
    check_te_b_high_forces_z_low: assert property (
        @(posedge clk) TE_B |-> (Z == 1'b0)
    );

// A low on TE_B must keep Z high.
    check_te_b_low_keeps_z_high: assert property (
        @(posedge clk) !TE_B |-> (Z == 1'b1)
    );

endmodule
