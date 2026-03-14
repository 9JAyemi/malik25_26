module shift_register_sva (
    input logic clk,
    input logic [3:0] in,
    input logic load,
    input logic [3:0] out,
    input logic valid
);
    ///// Functional next-state rules /////
    // Next out equals prior load ? prior in : prior out shifted in with 0 LSB.
    check_next_out_function: assert property (
        @(posedge clk) 1'b1 |=> (out == ($past(load) ? $past(in) : { $past(out[2:0]), 1'b0 }))
    );
    // When load is 1, next out equals prior in.
    check_load_captures_in_next: assert property (
        @(posedge clk) load |=> (out == $past(in))
    );
    // When load is 0, next out equals prior out shifted left with 0 inserted.
    check_no_load_shifts_next: assert property (
        @(posedge clk) !load |=> (out == { $past(out[2:0]), 1'b0 })
    );
    // When load is 0, the next out[0] must be 0.
    check_lsb_zero_on_shift: assert property (
        @(posedge clk) !load |=> (out[0] == 1'b0)
    );

    ///// Valid signaling /////
    // Next valid equals prior load.
    check_valid_follows_prev_load: assert property (
        @(posedge clk) 1'b1 |=> (valid == $past(load))
    );
    // When load is 1, next valid must be 1.
    check_load_sets_valid_next: assert property (
        @(posedge clk) load |=> (valid == 1'b1)
    );
    // If valid is 1 now, load was 1 in the prior cycle.
    check_valid_implies_prev_load: assert property (
        @(posedge clk) valid |-> $past(load)
    );
    // If valid is 1 now, out equals prior in (loaded last cycle).
    check_valid_implies_out_prev_in: assert property (
        @(posedge clk) valid |-> (out == $past(in))
    );

    ///// Long no-load behavior /////
    // After 4 consecutive cycles of no load, out becomes 0.
    check_no_load_flushes_zero_after_four: assert property (
        @(posedge clk) (!load)[*4] |=> (out == 4'b0000)
    );
endmodule