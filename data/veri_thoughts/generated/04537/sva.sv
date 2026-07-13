module EtherCAT_slave_sva #(
    parameter n = 8
) (
    input logic [n-1:0] in_receive,
    input logic         clk,
    input logic         rst,
    input logic [n-1:0] out_send
);

    // When reset is sampled high, the output register is cleared.
    check_reset_clears_output: assert property (
        @(posedge clk) rst |-> (out_send == {n{1'b0}})
    );

    // The first clock after reset release still sees the cleared output.
    check_post_reset_output_is_zero: assert property (
        @(posedge clk) disable iff ($initstate || rst)
        $past(rst) |-> (out_send == {n{1'b0}})
    );

    // In non-reset cycles, the sampled output is either zero or the prior sampled input.
    check_output_is_zero_or_prior_input: assert property (
        @(posedge clk) disable iff ($initstate || rst)
        ((out_send == {n{1'b0}}) || (out_send == $past(in_receive)))
    );

endmodule