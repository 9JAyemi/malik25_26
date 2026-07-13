module accumulator_sva (
    input logic clk,
    input logic rst,
    input logic [7:0] data_in,
    input logic [7:0] out
);

// Reset clears the accumulator on the next clock.
    check_reset_clears_out: assert property (
        @(posedge clk) rst |=> (out == 8'h00)
    );

// With reset low, the next output equals the previous input plus the previous output.
    check_accumulation: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (out == ($past(data_in) + $past(out)))
    );

// Adding zero leaves the accumulator unchanged.
    check_zero_input_holds_value: assert property (
        @(posedge clk) disable iff (rst) (data_in == 8'h00) |=> (out == $past(out))
    );

// Adding 0xFF wraps the accumulator from 0xFF to 0x00.
    check_ff_input_wraps_value: assert property (
        @(posedge clk) disable iff (rst) (data_in == 8'hFF) |=> (out == 8'h00)
    );

endmodule
