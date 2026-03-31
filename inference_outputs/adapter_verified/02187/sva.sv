module data_storage_sva (
    input logic        clk,
    input logic        reset,
    input logic [31:0] in_data,
    input logic        in_valid,
    input logic [31:0] out_data,
    input logic        out_valid
);

// Reset clears the stored data and output valid flag on the next cycle.
    check_reset_clears_outputs: assert property (
        @(posedge clk) reset |=> (out_data == 32'h0000_0000) && (out_valid == 1'b0)
    );

// A valid input updates the output data and raises the output valid flag on the next cycle.
    check_valid_input_updates_output: assert property (
        @(posedge clk) disable iff (reset)
        in_valid |=> (out_data == $past(in_data)) && (out_valid == 1'b1)
    );

// Without a valid input, the output valid flag is cleared on the next cycle.
    check_no_valid_input_clears_valid: assert property (
        @(posedge clk) disable iff (reset)
        !in_valid |=> (out_valid == 1'b0)
    );

// Output data holds its value when no valid input is received.
    check_no_valid_input_holds_data: assert property (
        @(posedge clk) disable iff (reset)
        !in_valid |=> (out_data == $past(out_data))
    );

endmodule
