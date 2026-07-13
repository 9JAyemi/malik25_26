module sum_4_bits_sva (
    input logic clk,            // formal clock for assertions
    input logic [15:0] in,
    input logic [3:0]  out
);
    ///// Functional mapping /////
    // out equals sum of high and low nibbles of in (4-bit wrap).
    check_functional_sum: assert property (
        @(posedge clk) out == (in[15:12] + in[3:0])
    );

    ///// Dependency on inputs /////
    // Changing only in[11:4] does not change out.
    check_mid_bits_do_not_affect_output: assert property (
        @(posedge clk)
            ( (in[15:12] == $past(in[15:12], 1, in[15:12])) &&
              (in[3:0]   == $past(in[3:0],   1, in[3:0]))   &&
              (in[11:4]  != $past(in[11:4],  1, in[11:4])) ) |-> 
            ( out == $past(out, 1, out) )
    );

    // out changes only if in[15:12] or in[3:0] changes.
    check_out_changes_only_if_relevant_input_changes: assert property (
        @(posedge clk)
            (out != $past(out, 1, out)) |-> 
            ( (in[15:12] != $past(in[15:12], 1, in[15:12])) || 
              (in[3:0]   != $past(in[3:0],   1, in[3:0])) )
    );

    ///// Stability /////
    // If in is stable, out is stable.
    check_stable_in_implies_stable_out: assert property (
        @(posedge clk) $stable(in) |-> $stable(out)
    );
endmodule