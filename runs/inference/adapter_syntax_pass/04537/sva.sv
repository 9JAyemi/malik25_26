module EtherCAT_slave_sva #(
    parameter n = 8
)(
    input logic [n-1:0] in_receive,
    input logic         clk,
    input logic         rst,
    input logic [n-1:0] out_send
);

    // Reset clears the output on the next clock.
    check_reset_clears_out_send: assert property (
        @(posedge clk) rst |=> (out_send == {n{1'b0}})
    );

    // The output is zero on the first clock after reset deasserts.
    check_reset_release_zero: assert property (
        @(posedge clk) disable iff (rst) $fell(rst) |-> (out_send == {n{1'b0}})
    );

    // The output is either zero or the previous cycle's input.
    check_out_send_is_zero_or_prev_input: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |-> ((out_send == {n{1'b0}}) || (out_send == $past(in_receive)))
    );

    // A nonzero output must match the previous cycle's input.
    check_nonzero_out_send_matches_prev_input: assert property (
        @(posedge clk) disable iff (rst) (out_send != {n{1'b0}}) |-> (out_send == $past(in_receive))
    );

endmodule