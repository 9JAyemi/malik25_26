module top_module_sva (
    input logic        clk,
    input logic        reset,
    input logic        load,
    input logic [7:0]  data_in,
    input logic        d,
    input logic [15:0] q
);

    // Reset drives the top-level output low on rising clock edges.
    check_reset_clears_output_on_posedge: assert property (
        @(posedge clk) reset |-> (q == 16'h0000)
    );

    // Reset drives the top-level output low on falling clock edges.
    check_reset_clears_output_on_negedge: assert property (
        @(negedge clk) reset |-> (q == 16'h0000)
    );

    // A load places data_in[6:0] into the visible upper q bits.
    check_load_copies_data_into_visible_upper_bits: assert property (
        @(posedge clk) disable iff (reset)
        load |=> (q[15:9] == $past(data_in[6:0]))
    );

    // A load moves the prior visible upper slice down into q[7:1].
    check_load_shifts_prior_visible_bits_down: assert property (
        @(posedge clk) disable iff (reset)
        load |=> (q[7:1] == $past(q[15:9]))
    );

    // Without load, the visible shift-register bits rotate forward.
    check_shift_rotates_visible_bits_when_not_loading: assert property (
        @(posedge clk) disable iff (reset)
        !load |=> (q[15:2] == $past(q[14:1]))
    );

    // The output LSB reflects the previous falling-edge sample of d.
    check_falling_edge_captures_d_into_output_lsb: assert property (
        @(negedge clk) disable iff (reset)
        1'b1 |=> (q[0] == $past(d))
    );

endmodule