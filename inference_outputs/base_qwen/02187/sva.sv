```systemverilog
module data_storage_sva (
    input logic clk,
    input logic reset,
    input logic [31:0] in_data,
    input logic in_valid,
    output logic [31:0] out_data,
    output logic out_valid
);
    // Reset behavior: out_valid should be 0 after reset
    reset_out_valid: assert property (
        @(posedge clk) disable iff (!reset) out_valid == 1'b0
    );

    // Data storage behavior: out_data should match stored_data when out_valid is 1
    data_storage: assert property (
        @(posedge clk) disable iff (!reset) (out_valid == 1'b1) |-> out_data == stored_data
    );

    // Input validation behavior: in_valid should not cause out_valid to be 1 when reset is active
    input_valid_reset: assert property (
        @(posedge clk) disable iff (!reset) (reset == 1'b1) |-> in_valid == 1'b0
    );

    // Data update behavior: stored_data should update when in_valid is 1 and reset is not active
    data_update: assert property (
        @(posedge clk) disable iff (!reset) (in_valid == 1'b1) |-> stored_data == in_data
    );

    // Output validity behavior: out_valid should be 0 when in_valid is 0 and reset is not active
    output_valid_no_input: assert property (
        @(posedge clk) disable iff (!reset) (in_valid == 1'b0) |-> out_valid == 1'b0
    );

    // Stored data behavior: stored_data should be 0 after reset
    stored_data_reset: assert property (
        @(posedge clk) disable iff (!reset) stored_data == 0
    );

    // Output data behavior: out_data should be 0 after reset
    output_data_reset: assert property (
        @(posedge clk) disable iff (!reset) out_data == 0
    );

    // Input data behavior: in_data should not affect out_data when reset is active
    input_data_reset: assert property (
        @(posedge clk) disable iff (!reset) (reset == 1'b1) |-> in_data == 0
    );

    // Output validity behavior: out_valid should be 1 when in_valid is 1 and reset is not active
    output_valid_input: assert property (
        @(posedge clk) disable iff (!reset) (in_valid == 1'b1) |-> out_valid == 1'b1
    );

    // Data storage behavior: out_data should match stored_data when out_valid is 1 and reset is not active
    data_storage_no_reset: assert property (
        @(posedge clk) disable iff (!reset) (out_valid == 1'b1) |-> out_data == stored_data
    );
endmodule
```