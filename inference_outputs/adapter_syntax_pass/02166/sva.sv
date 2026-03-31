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

    // The first cycle after reset deassertion still shows zero.
    check_reset_release_starts_from_zero: assert property (
        @(posedge clk) disable iff (rst) $fell(rst) |-> (out == 8'h00)
    );

    // The accumulator adds the previous cycle's input when reset is low.
    check_accumulator_adds_previous_input: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (out == ($past(out) + $past(data_in)))
    );

    // Zero input leaves the accumulator unchanged.
    check_zero_input_holds_value: assert property (
        @(posedge clk) disable iff (rst) (data_in == 8'h00) |=> (out == $past(out))
    );

    // All-ones input wraps the 8-bit accumulator.
    check_all_ones_input_wraps: assert property (
        @(posedge clk) disable iff (rst) (data_in == 8'hFF) |=> (out == ($past(out) + 8'hFF))
    );

endmodule