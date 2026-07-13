module barrel_shifter_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [1:0] S,
    input logic [3:0] B
);
    ///// Functional mapping (combinational, sampled on clk) /////
    // B matches the RTL expression for all A,S.
    check_functional_mapping: assert property (
        @(posedge clk)
            B == ( S[0]
                   ? ( (S[1] ? {2'b00, A[3], A[3]} : {A[1:0], A[3:2]}) >> 1 )
                   :   (S[1] ? {2'b00, A[3], A[3]} : {A[1:0], A[3:2]}) )
    );

    // For S == 2'b00: B = {A1, A0, A3, A2}.
    check_case_S_00: assert property (
        @(posedge clk) (S == 2'b00) |-> (B == {A[1], A[0], A[3], A[2]})
    );

    // For S == 2'b01: B = {0, A1, A0, A3}.
    check_case_S_01: assert property (
        @(posedge clk) (S == 2'b01) |-> (B == {1'b0, A[1], A[0], A[3]})
    );

    // For S == 2'b10: B = {0, 0, A3, A3}.
    check_case_S_10: assert property (
        @(posedge clk) (S == 2'b10) |-> (B == {2'b00, A[3], A[3]})
    );

    // For S == 2'b11: B = {0, 0, 0, A3}.
    check_case_S_11: assert property (
        @(posedge clk) (S == 2'b11) |-> (B == {3'b000, A[3]})
    );

    ///// Basic invariants derived from the RTL /////
    // When shifting by 1 (S[0]==1), B[3] must be 0 (logical right shift).
    check_shift1_msb_zero: assert property (
        @(posedge clk) S[0] |-> (B[3] == 1'b0)
    );

    // When S[1]==1, upper two bits of B are always 0 (due to temp composition).
    check_s1_upper_zero: assert property (
        @(posedge clk) S[1] |-> (B[3:2] == 2'b00)
    );

    // If inputs A and S are stable across cycles, B must be stable.
    check_stability_when_inputs_stable: assert property (
        @(posedge clk) $stable(A) && $stable(S) |-> $stable(B)
    );

    // For S == 2'b10, low two bits of B are identical.
    check_s10_lowpair_equal: assert property (
        @(posedge clk) (S == 2'b10) |-> (B[1] == B[0])
    );

    // For S == 2'b11, B[2:1] are 0.
    check_s11_mid_zero: assert property (
        @(posedge clk) (S == 2'b11) |-> (B[2:1] == 2'b00)
    );
endmodule