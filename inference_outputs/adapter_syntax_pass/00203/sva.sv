module BusHold_sva #(
    parameter n = 8
) (
    input logic [n-1:0] in,
    input logic         clk,
    input logic         rst,
    input logic [n-1:0] out
);

    // Reset clears the held value on the next clock.
    check_reset_clears_out: assert property (
        @(posedge clk) rst |=> (out == {n{1'b0}})
    );

    // With reset low, the held value captures the input on the next clock.
    check_capture_on_next_clock: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (out == $past(in))
    );

    // The held value holds its value when the input is unchanged.
    check_hold_when_input_unchanged: assert property (
        @(posedge clk) disable iff (rst) (in == $past(in)) |=> (out == $past(out))
    );

    // The held value changes when the input differs from the previous held value.
    check_update_when_input_changes: assert property (
        @(posedge clk) disable iff (rst) (in != $past(out)) |=> (out != $past(out))
    );

endmodule