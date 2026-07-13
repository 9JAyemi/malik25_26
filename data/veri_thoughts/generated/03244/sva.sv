module karnaugh_map_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic F
);

    // AB=00 selects D xor C.
    check_case_00_d_xor_c: assert property (
        @($global_clock) ({A,B} === 2'b00) |-> (F === (D ^ C))
    );

    // AB=01 selects B xor C.
    check_case_01_b_xor_c: assert property (
        @($global_clock) ({A,B} === 2'b01) |-> (F === (B ^ C))
    );

    // AB=11 selects C xor D.
    check_case_11_c_xor_d: assert property (
        @($global_clock) ({A,B} === 2'b11) |-> (F === (C ^ D))
    );

    // AB=10 selects A xor D.
    check_case_10_a_xor_d: assert property (
        @($global_clock) ({A,B} === 2'b10) |-> (F === (A ^ D))
    );

endmodule