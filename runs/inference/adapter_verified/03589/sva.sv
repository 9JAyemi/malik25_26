module addsub_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic SUB,
    input logic [3:0] OUT,
    input logic COUT
);

// No RTL reset; assertions are always active.

    // When SUB is low, OUT equals A + B.
    check_add_mode_result: assert property (
        @(posedge clk) !SUB |-> (OUT == (A + B))
    );

// When SUB is high, OUT equals A + (~B + 1).
    check_sub_mode_result: assert property (
        @(posedge clk) SUB |-> (OUT == (A + (~B + 4'b0001)))
    );

// In add mode, COUT is zero.
    check_add_mode_cout_zero: assert property (
        @(posedge clk) !SUB |-> (COUT == 1'b0)
    );

// In add mode, OUT is zero-extended to 4 bits.
    check_add_mode_zero_extend: assert property (
        @(posedge clk) !SUB |-> (OUT[3:1] == 3'b000)
    );

// In subtract mode, COUT equals A[3].
    check_sub_mode_cout_matches_a3: assert property (
        @(posedge clk) SUB |-> (COUT == A[3])
    );

// In subtract mode, OUT[3] equals A[3].
    check_sub_mode_msb_matches_a3: assert property (
        @(posedge clk) SUB |-> (OUT[3] == A[3])
    );

// In subtract mode, OUT[2:0] equals A[2:0] + (~B[2:0] + 3'b001).
    check_sub_mode_lsb3_matches_a3_b3: assert property (
        @(posedge clk) SUB |-> (OUT[2:0] == (A[2:0] + (~B[2:0] + 3'b001)))
    );

// In subtract mode, OUT equals A + (~B + 1) and COUT equals A[3].
    check_sub_mode_equivalence: assert property (
        @(posedge clk) SUB |-> (OUT == (A + (~B + 4'b0001))) && (COUT == A[3])
    );

// In add mode, OUT equals A + B and COUT is zero.
    check_add_mode_equivalence: assert property (
        @(posedge clk) !SUB |-> (OUT == (A + B)) && (COUT == 1'b0)
    );

endmodule
