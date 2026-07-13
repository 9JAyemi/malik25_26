module myModule_sva (
    input logic        CLK,
    input logic        ready_downstream,
    input logic        ready,
    input logic        reset,
    input logic [64:0] process_input,
    input logic [64:0] process_output
);

    // Reset drives ready low on the next cycle.
    check_reset_drives_ready_low: assert property (
        @(posedge CLK) reset |=> (ready == 1'b0)
    );

    // Reset clears process_output on the next cycle.
    check_reset_clears_process_output: assert property (
        @(posedge CLK) reset |=> (process_output == 65'd0)
    );

    // Any nonzero output change must coincide with ready asserted.
    check_nonzero_output_change_implies_ready: assert property (
        @(posedge CLK) disable iff (reset)
        (!$initstate && $changed(process_output) && (process_output != 65'd0)) |-> (ready == 1'b1)
    );

    // MSB-high output changes must capture the prior input bits.
    check_prefixed_output_uses_prior_input: assert property (
        @(posedge CLK) disable iff (reset)
        (!$initstate && $changed(process_output) && process_output[64]) |->
            ((ready == 1'b1) && (process_output == {1'b1, $past(process_input[63:0])}))
    );

    // MSB-low nonzero output changes must be the constant 1.
    check_msb_low_nonzero_output_is_one: assert property (
        @(posedge CLK) disable iff (reset)
        (!$initstate && $changed(process_output) && !process_output[64] && (process_output != 65'd0)) |->
            ((ready == 1'b1) && (process_output == 65'd1))
    );

    // An output change to 1 requires prior ready_downstream high.
    check_output_one_requires_prior_ready_downstream: assert property (
        @(posedge CLK) disable iff (reset)
        (!$initstate && $changed(process_output) && (process_output == 65'd1)) |->
            ((ready == 1'b1) && $past(ready_downstream))
    );

    // Any change to zero output must come from a reset cycle.
    check_zero_output_change_requires_reset: assert property (
        @(posedge CLK)
        (!$initstate && $changed(process_output) && (process_output == 65'd0)) |->
            ((ready == 1'b0) && $past(reset))
    );

    // ready low outside reset means process_output is held.
    check_ready_low_holds_process_output: assert property (
        @(posedge CLK) disable iff (reset)
        (!$initstate && !$past(reset) && (ready == 1'b0)) |-> $stable(process_output)
    );

    // A rising ready must present a nonzero output.
    check_ready_rise_has_nonzero_output: assert property (
        @(posedge CLK) disable iff (reset)
        (!$initstate && $rose(ready)) |-> (process_output != 65'd0)
    );

endmodule