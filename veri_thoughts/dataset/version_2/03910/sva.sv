module bv_count_sva #(
    parameter int width       = 64,
    parameter int width_count = 6,
    parameter int stage       = 1,
    parameter int range_end   = 1
) (
    input logic reset,
    input logic clk,
    input logic bv_valid,
    input logic [width-1:0] bv,
    input logic [width_count-1:0] count,
    input logic bv_out_valid,
    input logic [width-1:0] bv_out,
    input logic [width_count-1:0] count_out
);

    localparam logic [width_count-1:0] RANGE_END_COUNT = range_end;

    // Output valid follows the previous cycle's input valid.
    check_valid_follows_bv_valid: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        bv_out_valid == $past(bv_valid)
    );

    // Invalid input clears all registered outputs on the next cycle.
    check_invalid_clears_outputs: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        !$past(bv_valid) |-> (!bv_out_valid &&
                              (bv_out == {width{1'b0}}) &&
                              (count_out == {width_count{1'b0}}))
    );

    // Nonzero low bits pass the bit-vector through unchanged.
    check_passthrough_bv_on_nonzero_low_bits: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        $past(bv_valid) && $past(|(bv[range_end-1:0])) |-> (bv_out == $past(bv))
    );

    // Nonzero low bits preserve the count.
    check_passthrough_count_on_nonzero_low_bits: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        $past(bv_valid) && $past(|(bv[range_end-1:0])) |-> (count_out == $past(count))
    );

    // Zero low bits shift the bit-vector right by range_end.
    check_shift_bv_on_zero_low_bits: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        $past(bv_valid) && !$past(|(bv[range_end-1:0])) |-> (bv_out == ($past(bv) >> range_end))
    );

    // Zero low bits increment the count by range_end.
    check_increment_count_on_zero_low_bits: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        $past(bv_valid) && !$past(|(bv[range_end-1:0])) |-> (count_out == ($past(count) + RANGE_END_COUNT))
    );

    // When output valid is low, both data outputs are zero.
    check_zeroed_outputs_when_not_valid: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        !bv_out_valid |-> ((bv_out == {width{1'b0}}) &&
                           (count_out == {width_count{1'b0}}))
    );

    // Valid output must match one of the two implemented branches.
    check_valid_output_matches_selected_branch: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        bv_out_valid |-> ($past(bv_valid) &&
                          (($past(|(bv[range_end-1:0])) &&
                            (bv_out == $past(bv)) &&
                            (count_out == $past(count))) ||
                           (!$past(|(bv[range_end-1:0])) &&
                            (bv_out == ($past(bv) >> range_end)) &&
                            (count_out == ($past(count) + RANGE_END_COUNT)))))
    );

endmodule