module calculator_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [1:0] op,
    input logic [7:0] result
);
    // No clock/reset in DUT; combinational; assertions sample on any input edge.

    // op=00: result equals A+B (8-bit wrap).
    check_add_result: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or
          posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
          posedge A[4] or negedge A[4] or posedge A[5] or negedge A[5] or
          posedge A[6] or negedge A[6] or posedge A[7] or negedge A[7] or
          posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or
          posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
          posedge B[4] or negedge B[4] or posedge B[5] or negedge B[5] or
          posedge B[6] or negedge B[6] or posedge B[7] or negedge B[7] or
          posedge op[0] or negedge op[0] or posedge op[1] or negedge op[1])
        (op == 2'b00) |-> (result == (A + B))
    );

    // op=01: result equals A-B (8-bit wrap).
    check_sub_result: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or
          posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
          posedge A[4] or negedge A[4] or posedge A[5] or negedge A[5] or
          posedge A[6] or negedge A[6] or posedge A[7] or negedge A[7] or
          posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or
          posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
          posedge B[4] or negedge B[4] or posedge B[5] or negedge B[5] or
          posedge B[6] or negedge B[6] or posedge B[7] or negedge B[7] or
          posedge op[0] or negedge op[0] or posedge op[1] or negedge op[1])
        (op == 2'b01) |-> (result == (A - B))
    );

    // op=10: result equals A*B (8-bit wrap).
    check_mul_result: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or
          posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
          posedge A[4] or negedge A[4] or posedge A[5] or negedge A[5] or
          posedge A[6] or negedge A[6] or posedge A[7] or negedge A[7] or
          posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or
          posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
          posedge B[4] or negedge B[4] or posedge B[5] or negedge B[5] or
          posedge B[6] or negedge B[6] or posedge B[7] or negedge B[7] or
          posedge op[0] or negedge op[0] or posedge op[1] or negedge op[1])
        (op == 2'b10) |-> (result == (A * B))
    );

    // op=11 with B!=0: result equals A/B (8-bit wrap).
    check_div_nonzero_result: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or
          posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
          posedge A[4] or negedge A[4] or posedge A[5] or negedge A[5] or
          posedge A[6] or negedge A[6] or posedge A[7] or negedge A[7] or
          posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or
          posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
          posedge B[4] or negedge B[4] or posedge B[5] or negedge B[5] or
          posedge B[6] or negedge B[6] or posedge B[7] or negedge B[7] or
          posedge op[0] or negedge op[0] or posedge op[1] or negedge op[1])
        ((op == 2'b11) && (B != 8'd0)) |-> (result == (A / B))
    );

    // op=11 with B==0: result is 0.
    check_div_zero_result: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or
          posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
          posedge A[4] or negedge A[4] or posedge A[5] or negedge A[5] or
          posedge A[6] or negedge A[6] or posedge A[7] or negedge A[7] or
          posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or
          posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
          posedge B[4] or negedge B[4] or posedge B[5] or negedge B[5] or
          posedge B[6] or negedge B[6] or posedge B[7] or negedge B[7] or
          posedge op[0] or negedge op[0] or posedge op[1] or negedge op[1])
        ((op == 2'b11) && (B == 8'd0)) |-> (result == 8'd0)
    );

    // For op=11, result is always within 0..255 (no overflow).
    check_div_result_range: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or
          posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
          posedge A[4] or negedge A[4] or posedge A[5] or negedge A[5] or
          posedge A[6] or negedge A[6] or posedge A[7] or negedge A[7] or
          posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or
          posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3] or
          posedge B[4] or negedge B[4] or posedge B[5] or negedge B[5] or
          posedge B[6] or negedge B[6] or posedge B[7] or negedge B[7] or
          posedge op[0] or negedge op[0] or posedge op[1] or negedge op[1])
        (op == 2'b11) |-> (result <= 8'd255)
    );

    // For op=10, result is always within 0..255 (no overflow).
    check_mul_result_range: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1