module mux4to1_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] C,
    input logic [3:0] D,
    input logic S0,
    input logic S1,
    input logic Y
);
    // Y equals the LSB of the RTL mux expression.
    check_y_matches_rtl_expr_lsb: assert property (
        @(posedge S0 or negedge S0 or posedge S1 or negedge S1)
            Y == (((S1 & S0 & D) | (S1 & ~S0 & C) | (~S1 & S0 & B) | (~S1 & ~S0 & A))[0])
    );

    // When S1=0 and S0=0, Y equals A[0].
    check_sel_00_to_A0: assert property (
        @(posedge S0 or negedge S0 or posedge S1 or negedge S1)
            (~S1 && ~S0) |-> (Y == A[0])
    );

    // When S1=0 and S0=1, Y equals B[0].
    check_sel_01_to_B0: assert property (
        @(posedge S0 or negedge S0 or posedge S1 or negedge S1)
            (~S1 && S0) |-> (Y == B[0])
    );

    // When S1=1 and S0=0, Y equals C[0].
    check_sel_10_to_C0: assert property (
        @(posedge S0 or negedge S0 or posedge S1 or negedge S1)
            (S1 && ~S0) |-> (Y == C[0])
    );

    // When S1=1 and S0=1, Y equals D[0].
    check_sel_11_to_D0: assert property (
        @(posedge S0 or negedge S0 or posedge S1 or negedge S1)
            (S1 && S0) |-> (Y == D[0])
    );

    // If all LSBs are equal, Y must equal that common value.
    check_y_equal_when_all_lsbs_equal: assert property (
        @(posedge S0 or negedge S0 or posedge S1 or negedge S1)
            ((A[0] == B[0]) && (B[0] == C[0]) && (C[0] == D[0])) |-> (Y == A[0])
    );

    // If all LSBs are 0, Y must be 0 regardless of select.
    check_y_zero_when_all_lsbs_zero: assert property (
        @(posedge S0 or negedge S0 or posedge S1 or negedge S1)
            ((A[0] == 1'b0) && (B[0] == 1'b0) && (C[0] == 1'b0) && (D[0] == 1'b0)) |-> (Y == 1'b0)
    );

    // If all LSBs are 1, Y must be 1 regardless of select.
    check_y_one_when_all_lsbs_one: assert property (
        @(posedge S0 or negedge S0 or posedge S1 or negedge S1)
            ((A[0] == 1'b1) && (B[0] == 1'b1) && (C[0] == 1'b1) && (D[0] == 1'b1)) |-> (Y == 1'b1)
    );

    // Decode terms are mutually exclusive (only one select term can be 1).
    check_decode_onehot: assert property (
        @(posedge S0 or negedge S0 or posedge S1 or negedge S1)
          !((~S1 & ~S0) && (~S1 & S0)) &&
          !((~S1 & ~S0) && (S1 & ~S0)) &&
          !((~S1 & ~S0) && (S1 & S0)) &&
          !((~S1 & S0) && (S1 & ~S0)) &&
          !((~S1 & S0) && (S1 & S0)) &&
          !((S1 & ~S0) && (S1 & S0))
    );

    // Y equals nested ternary version of the mux on the LSB.
    check_mux_with_ternary_lsb: assert property (
        @(posedge S0 or negedge S0 or posedge S1 or negedge S1)
            Y == ( S1 ? ( S0 ? D[0] : C[0] ) : ( S0 ? B[0] : A[0] ) )
    );
endmodule