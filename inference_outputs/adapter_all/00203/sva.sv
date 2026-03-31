module BusHold_sva #(
    parameter n = 8
) (
    input logic [n-1:0] in,
    input logic         clk,
    input logic         rst,
    input logic [n-1:0] out
);

    // Reset clears the held output on the next clock.
    check_reset_clears_output: assert property (
        @(posedge clk) rst |=> (out == '0)
    );

    // With reset low, the held output captures the input on the next clock.
    check_capture_on_next_clock: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (out == $past(in))
    );

    // With reset low, the held output holds its value when the input is unchanged.
    check_hold_when_input_unchanged: assert property (
        @(posedge clk) disable iff (rst) (in == $past(in)) |=> (out == $past(out))
    );

    // With reset low, the held output changes only when the input changes.
    check_output_change_requires_input_change: assert property (
        @(posedge clk) disable iff (rst) (out != $past(out)) |-> (in != $past(in))
    );

endmodule