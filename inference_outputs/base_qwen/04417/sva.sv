```systemverilog
module barrel_shifter_sva (
    input logic [3:0] data,
    input logic [1:0] shift_amount,
    output logic [3:0] result
);
    // Sequential logic is not present, so we use @(posedge clk) for all assertions.

    // The result should match the expected value based on the shift_amount.
    shift_result: assert property (
        @(posedge clk) disable iff (!reset) (result == case(shift_amount)
            2'b00: data;
            2'b01: {data[2:0], 1'b0};
            2'b10: {data[1:0], 2'b00};
            2'b11: {data[0], 3'b000};
            default: 4'bxxxx;
        endcase)
    ) else $error("Shift result does not match expected value.");

    // The shift_amount should be within the valid range [0, 3].
    valid_shift_amount: assert property (
        @(posedge clk) disable iff (!reset) (shift_amount inside {[0:3]})
    ) else $error("Shift amount is out of valid range.");

    // The data should be within the valid range [0, 15].
    valid_data: assert property (
        @(posedge clk) disable iff (!reset) (data inside {[0:15]})
    ) else $error("Data is out of valid range.");

    // The result should be within the valid range [0, 15].
    valid_result: assert property (
        @(posedge clk) disable iff (!reset) (result inside {[0:15]})
    ) else $error("Result is out of valid range.");

    // The shift_amount should not change during the shift operation.
    stable_shift_amount: assert property (
        @(posedge clk) disable iff (!reset) (shift_amount == shift_amount)
    ) else $error("Shift amount changed during shift operation.");

    // The data should not change during the shift operation.
    stable_data: assert property (
        @(posedge clk) disable iff (!reset) (data == data)
    ) else $error("Data changed during shift operation.");

    // The result should not change during the shift operation.
    stable_result: assert property (
        @(posedge clk) disable iff (!reset) (result == result)
    ) else $error("Result changed during shift operation.");

    // The shift_amount should not be 2'b11 when data is 4'b0000.
    no_shift_on_zero: assert property (
        @(posedge clk) disable iff (!reset) (!(data == 4'b0000 && shift_amount == 2'b11))
    ) else $error("Shift amount 2'b11 is not allowed when data is 4'b0000.");

    // The shift_amount should not be 2'b10 when data is 4'b0001.
    no_shift_on_one: assert property (
        @(posedge clk) disable iff (!reset) (!(data == 4'b0001 && shift_amount == 2'b10))
    ) else $error("Shift amount 2'b10 is not allowed when data is 4'b0001.");

    // The shift_amount should not be 2'b01 when data is 4'b0010.
    no_shift_on_two: assert property (
        @(posedge clk) disable iff (!reset) (!(data == 4'b0010 && shift_amount == 2'b01))
    ) else $error("Shift amount 2'b01 is not allowed when data is 4'b0010.");

    // The shift_amount should not be 2'b00 when data is 4'b0011.
    no_shift_on_three: assert property (
        @(posedge clk) disable iff (!reset) (!(data == 4'b0011 && shift_amount == 2'b00))
    ) else $error("Shift amount 2'b00 is not allowed when data is 4'b0011.");
endmodule
```