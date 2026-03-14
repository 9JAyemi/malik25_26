module four_bit_mux_sva (
    input logic [3:0] A,
    input logic [1:0] S,
    input logic [3:0] X
);
    // Combinational module with no clock/reset; assertions sample on any input edge.

    // S=00 forces X=0000.
    check_s00_zero: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge S[0] or negedge S[0] or posedge S[1] or negedge S[1])
        (S == 2'b00) |=> (X == 4'b0000)
    );

    // S=01 forces X=1111.
    check_s01_ones: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge S[0] or negedge S[0] or posedge S[1] or negedge S[1])
        (S == 2'b01) |=> (X == 4'b1111)
    );

    // S=10 with A==1111 forces X=0000.
    check_s10_allones_to_zero: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge S[0] or negedge S[0] or posedge S[1] or negedge S[1])
        ((S == 2'b10) && (A == 4'b1111)) |=> (X == 4'b0000)
    );

    // S=10 with A!=1111 passes A through to X.
    check_s10_passthrough_else: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge S[0] or negedge S[0] or posedge S[1] or negedge S[1])
        ((S == 2'b10) && (A != 4'b1111)) |=> (X == A)
    );

    // S=11 with A==0000 forces X=1111.
    check_s11_allzeros_to_ones: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge S[0] or negedge S[0] or posedge S[1] or negedge S[1])
        ((S == 2'b11) && (A == 4'b0000)) |=> (X == 4'b1111)
    );

    // S=11 with A!=0000 passes A through to X.
    check_s11_passthrough_else: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge S[0] or negedge S[0] or posedge S[1] or negedge S[1])
        ((S == 2'b11) && (A != 4'b0000)) |=> (X == A)
    );

    // Under S=10, X differs from A only when A==1111 and then X==0000.
    check_s10_only_diff_on_allones: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge S[0] or negedge S[0] or posedge S[1] or negedge S[1])
        ((S == 2'b10) && (X != A)) |=> ((A == 4'b1111) && (X == 4'b0000))
    );

    // Under S=11, X differs from A only when A==0000 and then X==1111.
    check_s11_only_diff_on_allzeros: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge S[0] or negedge S[0] or posedge S[1] or negedge S[1])
        ((S == 2'b11) && (X != A)) |=> ((A == 4'b0000) && (X == 4'b1111))
    );

    // X equals the exact function of A and S as coded in the case statement.
    check_functional_equivalence: assert property (
        @(posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge S[0] or negedge S[0] or posedge S[1] or negedge S[1])
        X == ((S == 2'b00) ? 4'b0000 :
              (S == 2'b01) ? 4'b1111 :
              (S == 2'b10) ? ((A == 4'b1111) ? 4'b0000 : A) :
                             ((A == 4'b0000) ? 4'b1111 : A))
    );

endmodule