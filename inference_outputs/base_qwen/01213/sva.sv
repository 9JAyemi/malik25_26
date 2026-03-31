```systemverilog
module barrel_shifter_sva (
    input logic CLK,
    input logic [7:0] DATA,
    input logic [2:0] SHIFT_AMOUNT,
    input logic SHIFT_DIRECTION,
    output logic [7:0] SHIFTED_DATA
);
    // Sequential logic is not present, so we use @(posedge CLK) for all properties.

    // The shifted_data register should always be updated on the rising edge of the clock.
    always_ff @(posedge CLK) begin
        if (SHIFT_DIRECTION == 0) begin
            shifted_data <= DATA << SHIFT_AMOUNT;
        end else begin
            shifted_data <= DATA >> SHIFT_AMOUNT;
        end
    end

    // The SHIFTED_DATA output should always reflect the value of shifted_data.
    output_check: assert property (
        @(posedge CLK) SHIFTED_DATA == shifted_data
    );

    // The SHIFTED_DATA output should be a valid 8-bit value.
    valid_output: assert property (
        @(posedge CLK) SHIFTED_DATA inside {[0:255]}
    );

    // The SHIFT_AMOUNT should be a valid 3-bit value.
    valid_shift_amount: assert property (
        @(posedge CLK) SHIFT_AMOUNT inside {[0:7]}
    );

    // The SHIFT_DIRECTION should be either 0 or 1.
    valid_shift_direction: assert property (
        @(posedge CLK) SHIFT_DIRECTION inside {0, 1}
    );

    // The shifted_data register should not be driven directly from outside the module.
    no_direct_assignment: assert property (
        @(posedge CLK) disable iff (1'b1) shifted_data !== DATA << SHIFT_AMOUNT && shifted_data !== DATA >> SHIFT_AMOUNT
    );

endmodule
```