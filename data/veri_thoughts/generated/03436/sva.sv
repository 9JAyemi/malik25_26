module oh_mux4_sva #(parameter DW = 1) (
    input logic          sel3,
    input logic          sel2,
    input logic          sel1,
    input logic          sel0,
    input logic [DW-1:0] in3,
    input logic [DW-1:0] in2,
    input logic [DW-1:0] in1,
    input logic [DW-1:0] in0,
    input logic [DW-1:0] out
);

    // No clock or reset exists in the RTL; sample on the formal global clock.

    // Output matches the RTL masked-OR expression.
    check_out_matches_masked_or: assert property (
        @($global_clock) disable iff (1'b0)
        out == (({DW{sel0}} & in0) |
                ({DW{sel1}} & in1) |
                ({DW{sel2}} & in2) |
                ({DW{sel3}} & in3))
    );

    // With no selects asserted, the output is zero.
    check_no_select_drives_zero: assert property (
        @($global_clock) disable iff (1'b0)
        (!sel0 && !sel1 && !sel2 && !sel3) |-> (out == '0)
    );

    // With only sel0 asserted, the output equals in0.
    check_sel0_only_routes_in0: assert property (
        @($global_clock) disable iff (1'b0)
        (sel0 && !sel1 && !sel2 && !sel3) |-> (out == in0)
    );

    // With only sel1 asserted, the output equals in1.
    check_sel1_only_routes_in1: assert property (
        @($global_clock) disable iff (1'b0)
        (!sel0 && sel1 && !sel2 && !sel3) |-> (out == in1)
    );

    // With only sel2 asserted, the output equals in2.
    check_sel2_only_routes_in2: assert property (
        @($global_clock) disable iff (1'b0)
        (!sel0 && !sel1 && sel2 && !sel3) |-> (out == in2)
    );

    // With only sel3 asserted, the output equals in3.
    check_sel3_only_routes_in3: assert property (
        @($global_clock) disable iff (1'b0)
        (!sel0 && !sel1 && !sel2 && sel3) |-> (out == in3)
    );

    // With all selects asserted, the output is the OR of all inputs.
    check_all_selects_or_all_inputs: assert property (
        @($global_clock) disable iff (1'b0)
        (sel0 && sel1 && sel2 && sel3) |-> (out == (in0 | in1 | in2 | in3))
    );

endmodule