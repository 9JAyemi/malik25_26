module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [35:0] in,
    input logic [31:0] out,
    input logic [3:0] seq_out,
    input logic [31:0] change_out,
    input logic [31:0] final_out
);

    // Reset clears the sequential edge detector output.
    check_seq_out_reset: assert property (
        @(posedge clk) reset |=> (seq_out == 4'b0000)
    );

    // Reset clears the change detector output.
    check_change_out_reset: assert property (
        @(posedge clk) reset |=> (change_out == 32'b0)
    );

    // Reset clears the top-level output.
    check_out_reset: assert property (
        @(posedge clk) reset |=> (out == 32'b0)
    );

    // The functional module ORs the two internal outputs.
    check_final_out_or: assert property (
        @(posedge clk) disable iff (reset)
        (final_out == (seq_out | change_out))
    );

    // The top-level output mirrors the functional module output.
    check_out_matches_final_out: assert property (
        @(posedge clk) disable iff (reset)
        (out == final_out)
    );

    // The top-level output is always a superset of the change detector output.
    check_out_superset_of_change_out: assert property (
        @(posedge clk) disable iff (reset)
        ((out & ~change_out) == 32'b0)
    );

    // The top-level output is always a superset of the sequential edge output.
    check_out_superset_of_seq_out: assert property (
        @(posedge clk) disable iff (reset)
        ((out & ~seq_out) == 32'b0)
    );

    // A change detector bit set in the previous cycle appears in the top-level output.
    check_change_out_propagates_to_out: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && (change_out & ~$past(change_out))) |-> (out & ~$past(change_out))
    );

    // A sequential edge detector bit set in the previous cycle appears in the top-level output.
    check_seq_out_propagates_to_out: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && (seq_out & ~$past(seq_out))) |-> (out & ~$past(seq_out))
    );

    // A top-level output bit set in the previous cycle must come from the change detector or the edge detector.
    check_out_bit_has_valid_source: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && (out & ~$past(out))) |->
            ((($past(out) & ~$past(change_out)) & ~($past(out) & ~$past(seq_out))) == 32'b0)
    );

endmodule