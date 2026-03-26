module ogfx_sync_cell_sva (
    input logic clk,
    input logic rst,
    input logic data_in,
    input logic data_out
);

    // A sampled reset forces the output low by the next clock.
    check_reset_clears_output_by_next_clock: assert property (
        @(posedge clk) rst |=> (data_out == 1'b0)
    );

    // The first clock after reset release still has a low output.
    check_first_clock_after_reset_release_is_low: assert property (
        @(posedge clk) (rst ##1 !rst) |-> (data_out == 1'b0)
    );

    // The second clock after reset release still has a low output.
    check_second_clock_after_reset_release_is_low: assert property (
        @(posedge clk) (rst ##1 !rst ##1 !rst) |-> (data_out == 1'b0)
    );

    property p_two_cycle_input_to_output_delay;
        bit sampled_in;
        @(posedge clk) disable iff (rst)
            (1'b1, sampled_in = data_in) |=> ##1 (data_out == sampled_in);
    endproperty

    // Without reset interruption, data_out is data_in delayed by two clocks.
    check_two_cycle_input_to_output_delay: assert property (
        p_two_cycle_input_to_output_delay
    );

endmodule