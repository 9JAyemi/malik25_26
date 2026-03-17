module mux_4to1_case_assertions (
    input logic a,
    input logic b,
    input logic c,
    input logic d,
    input logic sel0,
    input logic sel1,
    input logic out
);

    // When select is 00, out must equal a.
    check_out_matches_a_when_sel_00: assert property (
        @($global_clock) ({sel1, sel0} == 2'b00) |-> (out == a)
    );

    // When select is 01, out must equal b.
    check_out_matches_b_when_sel_01: assert property (
        @($global_clock) ({sel1, sel0} == 2'b01) |-> (out == b)
    );

    // When select is 10, out must equal c.
    check_out_matches_c_when_sel_10: assert property (
        @($global_clock) ({sel1, sel0} == 2'b10) |-> (out == c)
    );

    // When select is 11, out must equal d.
    check_out_matches_d_when_sel_11: assert property (
        @($global_clock) ({sel1, sel0} == 2'b11) |-> (out == d)
    );

endmodule