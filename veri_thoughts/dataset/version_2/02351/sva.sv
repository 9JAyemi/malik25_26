module omsp_sync_cell_sva (
    input  logic clk,
    input  logic rst,        // active high
    input  logic data_in,
    input  logic data_out,
    input  logic [1:0] data_sync
);
    // Reset forces internal state low.
    reset_clears_data_sync: assert property (
        @(posedge clk) rst |-> (data_sync == 2'b00)
    );

    // Reset drives output low.
    reset_drives_data_out_low: assert property (
        @(posedge clk) rst |-> (data_out == 1'b0)
    );

    // Output mirrors MSB of synchronizer.
    connect_data_out_to_msb: assert property (
        @(posedge clk) disable iff (rst) (data_out == data_sync[1])
    );

    // On each clock (no reset), LSB captures input (post-update check).
    lsb_captures_input_postupdate: assert property (
        @(posedge clk) disable iff (rst) ##0 (data_sync[0] == data_in)
    );

    // On each clock (no reset), MSB shifts from previous LSB (post-update check).
    msb_shifts_from_prev_lsb_postupdate: assert property (
        @(posedge clk) disable iff (rst) ##0 (data_sync[1] == $past(data_sync[0]))
    );

    // Combined post-update check: {out, lsb} matches {prev lsb, in}.
    pair_update_consistency: assert property (
        @(posedge clk) disable iff (rst) ##0 ({data_out, data_sync[0]} == {$past(data_sync[0]), data_in})
    );

    // With no reset on current and previous cycle, output equals last cycle's input.
    one_cycle_input_to_output_delay: assert property (
        @(posedge clk) disable iff (rst) (!$initstate && !$past(rst)) |-> (data_out == $past(data_in))
    );

    // On reset deassertion edge, output is driven low that cycle.
    output_low_on_reset_fall: assert property (
        @(posedge clk) $fell(rst) |-> (data_out == 1'b0)
    );

    // While reset is held, state and output remain zero.
    hold_zeros_while_reset: assert property (
        @(posedge clk) (rst && $past(rst)) |-> (data_sync == 2'b00) && (data_out == 1'b0)
    );
endmodule