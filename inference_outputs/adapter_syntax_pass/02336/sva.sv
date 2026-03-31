module MUX4_1_SL_sva (
    input logic [1:0] Sel,
    input logic [3:0] S0,
    input logic [3:0] S1,
    input logic [3:0] S2,
    input logic [3:0] S3,
    input logic [3:0] out
);

    // out must match the RTL mux expression.
    check_mux_function: assert property (
        @($global_clock)
        out === (Sel[1] ? (Sel[0] ? S3 : S2) : (Sel[0] ? S1 : S0))
    );

    // When Sel is 00, out must select S0.
    check_sel_00_selects_s0: assert property (
        @($global_clock)
        (Sel === 2'b00) |-> (out === S0)
    );

    // When Sel is 01, out must select S1.
    check_sel_01_selects_s1: assert property (
        @($global_clock)
        (Sel === 2'b01) |-> (out === S1)
    );

    // When Sel is 10, out must select S2.
    check_sel_10_selects_s2: assert property (
        @($global_clock)
        (Sel === 2'b10) |-> (out === S2)
    );

    // When Sel is 11, out must select S3.
    check_sel_11_selects_s3: assert property (
        @($global_clock)
        (Sel === 2'b11) |-> (out === S3)
    );

endmodule