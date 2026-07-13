module adder_subtractor_sva (
    // DUT ports
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       C,
    input logic [3:0] out,
    // Sampling clock for SVA (DUT is combinational; no reset present)
    input logic       clk
);
    // When C==0, output equals A+B (4-bit wraparound).
    compute_add_correct: assert property (
        @(posedge clk) (C == 1'b0) |-> (out == (A + B))
    );

    // When C==1, output equals A-B (4-bit wraparound).
    compute_sub_correct: assert property (
        @(posedge clk) (C == 1'b1) |-> (out == (A - B))
    );

    // If both inputs are zero, output is zero (both modes).
    zero_when_both_zero: assert property (
        @(posedge clk) ((A == 4'd0) && (B == 4'd0)) |-> (out == 4'd0)
    );

    // In subtraction mode and A==B, output is zero.
    sub_equal_zero: assert property (
        @(posedge clk) (C == 1'b1 && (A == B)) |-> (out == 4'd0)
    );

    // In addition mode with B==0, output passes A.
    add_passthrough_b_zero: assert property (
        @(posedge clk) (C == 1'b0 && (B == 4'd0)) |-> (out == A)
    );

    // In subtraction mode with B==0, output passes A.
    sub_passthrough_b_zero: assert property (
        @(posedge clk) (C == 1'b1 && (B == 4'd0)) |-> (out == A)
    );

    // In addition mode with A==0, output passes B.
    add_passthrough_a_zero: assert property (
        @(posedge clk) (C == 1'b0 && (A == 4'd0)) |-> (out == B)
    );
endmodule