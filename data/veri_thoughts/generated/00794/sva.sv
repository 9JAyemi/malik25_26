module top_module_sva (
    input logic clk,
    input logic [15:0] in,
    input logic [7:0] out_hi,
    input logic [7:0] out_lo
);
    // out_hi captures the upper byte of 'in' on the next clock.
    check_out_hi_captures_upper: assert property (
        @(posedge clk) 1'b1 |=> (out_hi == $past(in[15:8]))
    );

    // out_lo captures the lower byte of 'in' on the next clock.
    check_out_lo_captures_lower: assert property (
        @(posedge clk) 1'b1 |=> (out_lo == $past(in[7:0]))
    );

    // Combined outputs match the previous cycle's full input word.
    check_concat_matches_prev_in: assert property (
        @(posedge clk) 1'b1 |=> ({out_hi, out_lo} == $past(in))
    );

    // out_hi changes only if the previous cycle's upper byte changed vs two cycles ago.
    check_out_hi_change_implies_prev_in_hi_change: assert property (
        @(posedge clk) 1'b1 |=> ((out_hi != $past(out_hi)) |-> ($past(in[15:8]) != $past(in[15:8],2)))
    );

    // out_lo changes only if the previous cycle's lower byte changed vs two cycles ago.
    check_out_lo_change_implies_prev_in_lo_change: assert property (
        @(posedge clk) 1'b1 |=> ((out_lo != $past(out_lo)) |-> ($past(in[7:0]) != $past(in[7:0],2)))
    );

    // If only the lower byte changed two cycles to one cycle ago, out_hi remains unchanged this cycle.
    check_hi_unchanged_when_only_lo_changes: assert property (
        @(posedge clk) 1'b1 |=> ((($past(in[15:8]) == $past(in[15:8],2)) && ($past(in[7:0]) != $past(in[7:0],2))) |-> (out_hi == $past(out_hi)))
    );

    // If only the upper byte changed two cycles to one cycle ago, out_lo remains unchanged this cycle.
    check_lo_unchanged_when_only_hi_changes: assert property (
        @(posedge clk) 1'b1 |=> ((($past(in[7:0]) == $past(in[7:0],2)) && ($past(in[15:8]) != $past(in[15:8],2))) |-> (out_lo == $past(out_lo)))
    );
endmodule