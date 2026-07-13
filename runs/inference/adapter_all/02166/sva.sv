module accumulator_sva (
    input logic clk,
    input logic rst,
    input logic [7:0] data_in,
    input logic [7:0] out
);

    // Reset clears the accumulator output on the next clock.
    check_reset_clears_out: assert property (
        @(posedge clk) rst |=> (out == 8'h00)
    );

    // With reset low, the accumulator output increments by data_in each cycle.
    check_accumulates_each_cycle: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (out == ($past(out) + $past(data_in)))
    );

    // A zero input leaves the accumulator output unchanged.
    check_zero_input_holds: assert property (
        @(posedge clk) disable iff (rst) (data_in == 8'h00) |=> (out == $past(out))
    );

    // An all-ones input makes the accumulator output wrap from 8'hFF to 8'h00.
    check_all_ones_wraps: assert property (
        @(posedge clk) disable iff (rst) (data_in == 8'hFF) |=> (out == 8'h00)
    );

endmodule