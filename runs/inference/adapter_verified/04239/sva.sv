module sky130_fd_sc_hd__xor2_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B
);

// X equals A ^ B on each sampled clock edge.
    check_xor_function: assert property (
        @(posedge clk) X == (A ^ B)
    );

// When A equals B, X must be 0.
    check_equal_inputs_drive_zero: assert property (
        @(posedge clk) (A == B) |-> (X == 1'b0)
    );

// When A differs from B, X must be 1.
    check_different_inputs_drive_one: assert property (
        @(posedge clk) (A != B) |-> (X == 1'b1)
    );

// A=0 and B=0 implies X=0.
    check_zero_inputs_drive_zero: assert property (
        @(posedge clk) ((A == 1'b0) && (B == 1'b0)) |-> (X == 1'b0)
    );

// A=1 and B=1 implies X=0.
    check_one_inputs_drive_zero: assert property (
        @(posedge clk) ((A == 1'b1) && (B == 1'b1)) |-> (X == 1'b0)
    );

// A=0 and B=1 implies X=1.
    check_mismatch_01_drives_one: assert property (
        @(posedge clk) ((A == 1'b0) && (B == 1'b1)) |-> (X == 1'b1)
    );

// A=1 and B=0 implies X=1.
    check_mismatch_10_drives_one: assert property (
        @(posedge clk) ((A == 1'b1) && (B == 1'b0)) |-> (X == 1'b1)
    );

endmodule
