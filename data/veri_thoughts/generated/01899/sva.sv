module ResetEither_sva (
    input logic A_RST,
    input logic B_RST,
    input logic RST_OUT
);
    // Combinational reset combiner; sample on any edge of A_RST/B_RST.
    // Reset active level is `BSV_RESET_VALUE (1 if `BSV_POSITIVE_RESET, else 0).

    // Define `BSV_RESET_VALUE here only if not already defined.
`ifndef BSV_RESET_VALUE
`ifdef BSV_POSITIVE_RESET
    `define BSV_RESET_VALUE 1'b1
`else
    `define BSV_RESET_VALUE 1'b0
`endif
`endif

    // RST_OUT implements ((A==RV)||(B==RV)) ? RV : ~RV.
    check_function_equivalence: assert property (
        @(posedge A_RST or negedge A_RST or posedge B_RST or negedge B_RST)
        disable iff (1'b0)
        RST_OUT == (((A_RST == `BSV_RESET_VALUE) || (B_RST == `BSV_RESET_VALUE)) ? `BSV_RESET_VALUE : ~`BSV_RESET_VALUE)
    );

`ifdef BSV_POSITIVE_RESET
    // Active-high reset: output equals A_RST OR B_RST.
    check_active_high_or: assert property (
        @(posedge A_RST or negedge A_RST or posedge B_RST or negedge B_RST)
        disable iff (1'b0)
        RST_OUT == (A_RST || B_RST)
    );
`else
    // Active-low reset: output equals A_RST AND B_RST.
    check_active_low_and: assert property (
        @(posedge A_RST or negedge A_RST or posedge B_RST or negedge B_RST)
        disable iff (1'b0)
        RST_OUT == (A_RST && B_RST)
    );
`endif

    // If A_RST is asserted, RST_OUT must be asserted.
    check_assert_when_A_asserted: assert property (
        @(posedge A_RST or negedge A_RST)
        disable iff (1'b0)
        (A_RST == `BSV_RESET_VALUE) |-> (RST_OUT == `BSV_RESET_VALUE)
    );

    // If B_RST is asserted, RST_OUT must be asserted.
    check_assert_when_B_asserted: assert property (
        @(posedge B_RST or negedge B_RST)
        disable iff (1'b0)
        (B_RST == `BSV_RESET_VALUE) |-> (RST_OUT == `BSV_RESET_VALUE)
    );

    // If both deasserted, RST_OUT must be deasserted.
    check_deassert_when_both_deasserted: assert property (
        @(posedge A_RST or negedge A_RST or posedge B_RST or negedge B_RST)
        disable iff (1'b0)
        ((A_RST != `BSV_RESET_VALUE) && (B_RST != `BSV_RESET_VALUE)) |-> (RST_OUT != `BSV_RESET_VALUE)
    );

    // RST_OUT asserted only if at least one input is asserted.
    check_asserted_only_if_input_asserted: assert property (
        @(posedge A_RST or negedge A_RST or posedge B_RST or negedge B_RST)
        disable iff (1'b0)
        (RST_OUT == `BSV_RESET_VALUE) |-> ((A_RST == `BSV_RESET_VALUE) || (B_RST == `BSV_RESET_VALUE))
    );

    // RST_OUT deasserted only if both inputs are deasserted.
    check_deasserted_only_if_both_deasserted: assert property (
        @(posedge A_RST or negedge A_RST or posedge B_RST or negedge B_RST)
        disable iff (1'b0)
        (RST_OUT != `BSV_RESET_VALUE) |-> ((A_RST != `BSV_RESET_VALUE) && (B_RST != `BSV_RESET_VALUE))
    );

    // No X/Z on output when inputs are known 0/1.
    check_no_unknown_propagation: assert property (
        @(posedge A_RST or negedge A_RST or posedge B_RST or negedge B_RST)
        disable iff (1'b0)
        (!$isunknown({A_RST, B_RST})) |-> (!$isunknown(RST_OUT))
    );

endmodule