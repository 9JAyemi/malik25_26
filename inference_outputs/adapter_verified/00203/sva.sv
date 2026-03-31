module BusHold_sva (
    input logic [n-1:0] in,
    input logic clk,
    input logic rst,
    input logic [n-1:0] out
);

// Reset clears the held value on the next clock.
    check_reset_clears_out: assert property (
        @(posedge clk) rst |=> (out == 0)
    );

// With reset low, out captures in on the next rising edge.
    check_capture_on_posedge: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (out == $past(in))
    );

// With reset low, out holds its value when in is stable.
    check_hold_when_input_stable: assert property (
        @(posedge clk) disable iff (rst) $stable(in) |=> (out == $past(out))
    );

// With reset low, out changes when in differs from its previous value.
    check_update_when_input_changes: assert property (
        @(posedge clk) disable iff (rst) !$stable(in) |=> (out != $past(out))
    );

endmodule
