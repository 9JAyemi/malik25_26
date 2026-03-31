module EtherCAT_slave_sva #(
    parameter n = 8
)(
    input logic [n-1:0] in_receive,
    input logic         clk,
    input logic         rst,
    input logic [n-1:0] out_send
);

    // Reset forces the output to zero.
    check_reset_clears_output: assert property (
        @(posedge clk) rst |-> (out_send == '0)
    );

    // The output reflects the input from the previous clock.
    check_output_tracks_previous_input: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (out_send == $past(in_receive))
    );

    // A zero input is preserved on the next clock.
    check_zero_input_preserved: assert property (
        @(posedge clk) disable iff (rst)
        (in_receive == '0) |=> (out_send == '0)
    );

    // A zero output must come from a zero input on the previous clock.
    check_zero_output_requires_zero_input: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> ((out_send == '0) |-> ($past(in_receive) == '0))
    );

endmodule