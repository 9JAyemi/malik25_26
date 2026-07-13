module EtherCAT_slave_sva (
    input logic [n-1:0] in_receive,
    input logic clk,
    input logic rst,
    input logic [n-1:0] out_send
);

// Reset drives out_send to zero on the next clock.
    check_reset_clears_out_send: assert property (
        @(posedge clk) rst |=> (out_send == 0)
    );

// When not in reset, out_send captures in_receive on the next clock.
    check_capture_on_next_clock: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (out_send == $past(in_receive))
    );

// When not in reset, out_send equals in_receive on the current clock.
    check_capture_on_current_clock: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |-> (out_send == in_receive)
    );

endmodule
