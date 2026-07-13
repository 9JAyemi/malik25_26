module FFType_sva (
    input logic clock,
    input logic reset,
    input logic io_in,
    input logic io_init,
    input logic io_out,
    input logic io_enable
);

// Reset drives io_out to io_init on the next clock.
    check_reset_sets_output: assert property (
        @(posedge clock) reset |=> (io_out == $past(io_init))
    );

// With enable high, io_out captures io_in on the next clock.
    check_enable_captures_input: assert property (
        @(posedge clock) disable iff (reset) io_enable |=> (io_out == $past(io_in))
    );

// With enable low, io_out holds its previous value.
    check_disable_holds_output: assert property (
        @(posedge clock) disable iff (reset) !io_enable |=> (io_out == $past(io_out))
    );

// When enabled and io_in equals io_out, io_out remains unchanged.
    check_enable_no_change_when_input_matches_output: assert property (
        @(posedge clock) disable iff (reset) (io_enable && (io_in == io_out)) |=> (io_out == $past(io_out))
    );

// When enabled and io_in differs from io_out, io_out updates to io_in.
    check_enable_updates_output_when_input_differs: assert property (
        @(posedge clock) disable iff (reset) (io_enable && (io_in != io_out)) |=> (io_out == $past(io_in))
    );

endmodule
