module mux4to1_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic [1:0] S,
    input logic Y
);
    // Analysis: no clock/reset in RTL; pure combinational mux; sample assertions on input edges.

    // Y must equal the RTL sum-of-products implementation.
    check_sop_equivalence: assert property (
        @(posedge A or posedge B or posedge C or posedge D or posedge S[0] or posedge S[1])
        Y == ((A & (~S[1]) & (~S[0])) |
              (B & (~S[1]) &  S[0])  |
              (C &  S[1]  & (~S[0])) |
              (D &  S[1]  &  S[0]))
    );

    // When S==2'b00, Y must equal A.
    check_select_00_A: assert property (
        @(posedge A or posedge B or posedge C or posedge D or posedge S[0] or posedge S[1])
        (S == 2'b00) |-> (Y == A)
    );

    // When S==2'b01, Y must equal B.
    check_select_01_B: assert property (
        @(posedge A or posedge B or posedge C or posedge D or posedge S[0] or posedge S[1])
        (S == 2'b01) |-> (Y == B)
    );

    // When S==2'b10, Y must equal C.
    check_select_10_C: assert property (
        @(posedge A or posedge B or posedge C or posedge D or posedge S[0] or posedge S[1])
        (S == 2'b10) |-> (Y == C)
    );

    // When S==2'b11, Y must equal D.
    check_select_11_D: assert property (
        @(posedge A or posedge B or posedge C or posedge D or posedge S[0] or posedge S[1])
        (S == 2'b11) |-> (Y == D)
    );

    // If all data inputs are 0, Y must be 0 for any S.
    check_all_zero_inputs: assert property (
        @(posedge A or posedge B or posedge C or posedge D or posedge S[0] or posedge S[1])
        ((A==1'b0) && (B==1'b0) && (C==1'b0) && (D==1'b0)) |-> (Y==1'b0)
    );

    // If all data inputs are 1, Y must be 1 for any S.
    check_all_one_inputs: assert property (
        @(posedge A or posedge B or posedge C or posedge D or posedge S[0] or posedge S[1])
        ((A==1'b1) && (B==1'b1) && (C==1'b1) && (D==1'b1)) |-> (Y==1'b1)
    );
endmodule