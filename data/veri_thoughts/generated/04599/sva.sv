module barrel_shifter_assertions (
    input logic clk,
    input logic reset,
    input logic [31:0] data_in,
    input logic [4:0] shift_amount,
    input logic [31:0] data_out
);

    // Reset drives the registered output to zero on the next cycle.
    check_reset_clears_output: assert property (
        @(posedge clk) disable iff ($initstate)
        reset |=> (data_out == 32'b0)
    );

    // The first cycle after reset deassertion still shows the reset value.
    check_reset_release_zero: assert property (
        @(posedge clk) disable iff ($initstate)
        $fell(reset) |-> (data_out == 32'b0)
    );

    // A zero shift amount passes the previous cycle's input unchanged.
    check_zero_shift_passthrough: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (!$past(reset) && ($past(shift_amount) == 5'd0)) |-> (data_out == $past(data_in))
    );

    // Any nonzero unsigned shift amount produces a left shift of the previous input.
    check_nonzero_shift_left: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (!$past(reset) && ($past(shift_amount) != 5'd0)) |-> (data_out == ($past(data_in) << $past(shift_amount)))
    );

endmodule