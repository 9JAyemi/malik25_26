module sync_bits_sva
#(
    parameter NUM_OF_BITS = 1,
    parameter ASYNC_CLK   = 1
)
(
    input logic [NUM_OF_BITS-1:0] in,
    input logic                   out_resetn,
    input logic                   out_clk,
    input logic [NUM_OF_BITS-1:0] out,
    input logic [NUM_OF_BITS-1:0] cdc_sync_stage1,
    input logic [NUM_OF_BITS-1:0] cdc_sync_stage2
);

    // Stage1 captures the input on each active clock.
    check_stage1_captures_input: assert property (
        @(posedge out_clk) disable iff (!out_resetn)
        $past(out_resetn) |-> (cdc_sync_stage1 == $past(in))
    );

    // Stage2 captures the previous stage1 value on each active clock.
    check_stage2_captures_stage1: assert property (
        @(posedge out_clk) disable iff (!out_resetn)
        $past(out_resetn) |-> (cdc_sync_stage2 == $past(cdc_sync_stage1))
    );

    // Stage2 reflects the input after two active clocks.
    check_stage2_two_cycle_delay: assert property (
        @(posedge out_clk) disable iff (!out_resetn)
        ($past(out_resetn) && $past(out_resetn, 2)) |-> (cdc_sync_stage2 == $past(in, 2))
    );

    // A reset cycle clears both synchronizer stages.
    check_reset_clears_stages: assert property (
        @(posedge out_clk) disable iff (!out_resetn)
        $past(!out_resetn) |-> ((cdc_sync_stage1 == '0) && (cdc_sync_stage2 == '0))
    );

    generate
        if (ASYNC_CLK) begin : gen_async_clk_asserts
            // In async mode, output comes from the second synchronizer stage.
            check_async_out_from_stage2: assert property (
                @(posedge out_clk) disable iff (!out_resetn)
                (out == cdc_sync_stage2)
            );

            // In async mode, output reflects the input after two active clocks.
            check_async_out_two_cycle_delay: assert property (
                @(posedge out_clk) disable iff (!out_resetn)
                ($past(out_resetn) && $past(out_resetn, 2)) |-> (out == $past(in, 2))
            );

            // A reset cycle drives the async output low.
            check_async_reset_drives_out_low: assert property (
                @(posedge out_clk) disable iff (!out_resetn)
                $past(!out_resetn) |-> (out == '0)
            );
        end else begin : gen_direct_clk_asserts
            // In direct mode, output bypasses the synchronizer.
            check_direct_out_matches_input: assert property (
                @(posedge out_clk) disable iff (!out_resetn)
                (out == in)
            );
        end
    endgenerate

endmodule