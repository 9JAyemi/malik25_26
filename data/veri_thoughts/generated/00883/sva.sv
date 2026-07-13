module mux_stall_sva (
    input  logic               clk,          // sampling clock for SVA (DUT has no clock)
    input  logic [22:0]        cw_from_cu,
    input  logic               mux_op,
    input  logic [22:0]        cw_from_mux,
    input  logic               n2            // internal alias of mux_op
);
    // Clock: none in DUT; Reset: none in DUT; Logic: combinational; Behavior: cw_from_mux = cw_from_cu & mux_op.

    // Output equals input masked by mux_op (vector check).
    check_mask_vector: assert property (
        @(posedge clk) cw_from_mux == (cw_from_cu & {23{mux_op}})
    );

    // When mux_op is 0, output is all zeros.
    check_zero_when_disabled: assert property (
        @(posedge clk) (mux_op == 1'b0) |-> (cw_from_mux == 23'b0)
    );

    // When mux_op is 1, output equals input.
    check_pass_through_when_enabled: assert property (
        @(posedge clk) (mux_op == 1'b1) |-> (cw_from_mux == cw_from_cu)
    );

    // Output has no 1s where input has 0s (subset relationship).
    check_output_subset_of_input: assert property (
        @(posedge clk) ((cw_from_mux & ~cw_from_cu) == 23'b0)
    );

    // Internal alias n2 equals mux_op.
    check_n2_alias: assert property (
        @(posedge clk) (n2 == mux_op)
    );

    // Output equals input masked by internal n2 (redundant cross-check).
    check_mask_vector_using_n2: assert property (
        @(posedge clk) cw_from_mux == (cw_from_cu & {23{n2}})
    );

    // If inputs are stable across a cycle, output is stable.
    check_stability_when_inputs_stable: assert property (
        @(posedge clk) ($stable(cw_from_cu) && $stable(mux_op)) |=> $stable(cw_from_mux)
    );

    // If the input bus is all zeros, output must be zero for any mux_op.
    check_zero_when_input_zero: assert property (
        @(posedge clk) (cw_from_cu == 23'b0) |-> (cw_from_mux == 23'b0)
    );

endmodule