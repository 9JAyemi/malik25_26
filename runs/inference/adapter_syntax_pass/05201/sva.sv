module binary_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Cin,
    input logic       En,
    input logic [3:0] S,
    input logic       Cout
);

    // S is zero-extended when the enable is low.
    check_s_zero_when_disabled: assert property (
        @($global_clock) (!En) |-> (S == 4'b0000)
    );

    // S matches the enabled add result.
    check_s_matches_enabled_add: assert property (
        @($global_clock) En |-> (S == (A + B + Cin))
    );

    // Cout is always low in this RTL.
    check_cout_always_low: assert property (
        @($global_clock) (Cout == 1'b0)
    );

    // The least-significant sum bit is the enabled add of A[0], B[0], and Cin.
    check_lsb_sum_when_enabled: assert property (
        @($global_clock) En |-> (S[0] == (A[0] ^ B[0] ^ Cin))
    );

    // The least-significant sum bit is zero when the enable is low.
    check_lsb_zero_when_disabled: assert property (
        @($global_clock) (!En) |-> (S[0] == 1'b0)
    );

endmodule