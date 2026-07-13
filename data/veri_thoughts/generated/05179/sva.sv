module mux4_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] C,
    input logic [3:0] D,
    input logic [1:0] S,
    input logic       Y
);

    // No RTL clock or reset; sample this combinational mux on the formal global clock.

    // S=00 selects the LSB of A onto Y.
    check_select_a_lsb: assert property (
        @($global_clock) (S == 2'b00) |-> (Y == A[0])
    );

    // S=01 selects the LSB of B onto Y.
    check_select_b_lsb: assert property (
        @($global_clock) (S == 2'b01) |-> (Y == B[0])
    );

    // S=10 selects the LSB of C onto Y.
    check_select_c_lsb: assert property (
        @($global_clock) (S == 2'b10) |-> (Y == C[0])
    );

    // S=11 selects the LSB of D onto Y.
    check_select_d_lsb: assert property (
        @($global_clock) (S == 2'b11) |-> (Y == D[0])
    );

endmodule