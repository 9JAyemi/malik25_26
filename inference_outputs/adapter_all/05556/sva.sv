module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [35:0] in,
    input logic [31:0] out,
    input logic [3:0] seq_out,
    input logic [31:0] change_out,
    input logic [31:0] final_out
);

    // Reset clears all registered outputs.
    check_reset_clears_outputs: assert property (
        @(posedge clk) reset |-> ((out == 32'b0) && (seq_out == 4'b0) && (change_out == 32'b0) && (final_out == 32'b0))
    );

    // seq_out reflects the previous cycle's input nibble when the input changed.
    check_seq_out_on_input_change: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && (in[3:0] != $past(in[3:0]))) |-> (seq_out == $past(in[3:0]))
    );

    // seq_out holds its value when the input nibble did not change.
    check_seq_out_stable_on_input_stable: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && (in[3:0] == $past(in[3:0]))) |-> (seq_out == $past(seq_out))
    );

    // change_out is the previous cycle's masked input change vector.
    check_change_out_masked_vector: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate) |-> (change_out == ($past(in[35:4]) & ~$past(in[35:4])))
    );

    // final_out is the bitwise OR of seq_out and change_out.
    check_final_out_is_or_of_parts: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate) |-> (final_out == (seq_out | change_out))
    );

    // final_out matches the top-level output assignment.
    check_final_out_matches_out: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate) |-> (final_out == out)
    );

    // A change on the masked input bits appears in change_out.
    check_change_out_reflects_masked_change: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && ($past(in[35:4]) != $past(in[35:4], 2))) |-> (change_out == ($past(in[35:4], 1) & ~$past(in[35:4], 2)))
    );

    // A stable masked input vector keeps change_out stable.
    check_change_out_stable_on_masked_stable: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && ($past(in[35:4]) == $past(in[35:4], 2))) |-> (change_out == $past(change_out))
    );

endmodule