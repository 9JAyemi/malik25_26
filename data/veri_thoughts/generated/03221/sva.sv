module parity_check_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] data_in,
    input logic parity_out
);

    // After reset deasserts, parity_out is still cleared on that clock edge.
    check_reset_release_clears_output: assert property (
        @(posedge clk) disable iff (reset)
        $fell(reset) |-> (parity_out == 1'b0)
    );

    // Even input parity drives parity_out high on the next clock.
    check_even_parity_sets_output: assert property (
        @(posedge clk) disable iff (reset)
        (~^data_in) |=> (parity_out == 1'b1)
    );

    // Odd input parity drives parity_out low on the next clock.
    check_odd_parity_clears_output: assert property (
        @(posedge clk) disable iff (reset)
        (^data_in) |=> (parity_out == 1'b0)
    );

endmodule