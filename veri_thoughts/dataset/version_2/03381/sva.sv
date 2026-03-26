module add_sub_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       C,
    input logic [3:0] S,
    input logic [3:0] D
);

    // In add mode, S reflects the 4-bit result of A + B.
    check_s_add_mode: assert property (
        @($global_clock) (!C) |-> (S == (A + B))
    );

    // In subtract mode, S reflects the 4-bit result of A - B.
    check_s_sub_mode: assert property (
        @($global_clock) C |-> (S == (A - B))
    );

    // In add mode, D reflects the same 4-bit result of A + B.
    check_d_add_mode: assert property (
        @($global_clock) (!C) |-> (D == (A + B))
    );

    // In subtract mode, D reflects the same 4-bit result of A - B.
    check_d_sub_mode: assert property (
        @($global_clock) C |-> (D == (A - B))
    );

    // D always matches S for all input combinations.
    check_outputs_match: assert property (
        @($global_clock) D == S
    );

endmodule