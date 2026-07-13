module data_storage_sva (
    input logic clk,
    input logic reset,
    input logic [31:0] in_data,
    input logic in_valid,
    input logic [31:0] out_data,
    input logic out_valid
);

    // Reset clears the stored data and deasserts the output valid signal.
    check_reset_clears_outputs: assert property (
        @(posedge clk) reset |-> ((out_data == 32'h00000000) && (out_valid == 1'b0))
    );

    // A valid input updates the output data on the next cycle.
    check_valid_input_updates_output_data: assert property (
        @(posedge clk) disable iff (reset) in_valid |=> (out_data == $past(in_data))
    );

    // A valid input sets the output valid signal on the next cycle.
    check_valid_input_sets_output_valid: assert property (
        @(posedge clk) disable iff (reset) in_valid |=> (out_valid == 1'b1)
    );

    // A non-valid input clears the output valid signal on the next cycle.
    check_nonvalid_input_clears_output_valid: assert property (
        @(posedge clk) disable iff (reset) !in_valid |=> (out_valid == 1'b0)
    );

    // The output data holds when no valid input is present.
    check_nonvalid_input_holds_output_data: assert property (
        @(posedge clk) disable iff (reset) !in_valid |=> (out_data == $past(out_data))
    );

endmodule