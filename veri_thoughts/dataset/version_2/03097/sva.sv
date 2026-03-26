module switch_reader_sva (
    input logic       clk,
    input logic       reset_n,
    input logic [3:0] switches,
    input logic [3:0] data_out
);

    // Active-low reset clears the registered output.
    check_reset_clears_data_out: assert property (
        @(posedge clk) !reset_n |-> (data_out == 4'b0000)
    );

    // Each active clock loads data_out with the prior sampled switches value.
    check_data_out_captures_switches: assert property (
        @(posedge clk) disable iff (!reset_n)
        1'b1 |=> (data_out == $past(switches))
    );

    // After reset deasserts, data_out remains cleared until the next clocked update.
    check_reset_release_holds_zero_until_update: assert property (
        @(posedge clk) disable iff (!reset_n)
        $rose(reset_n) |-> (data_out == 4'b0000)
    );

endmodule