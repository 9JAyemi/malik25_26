module top_module_sva (
    input logic clk,
    input logic rst_n,
    input logic [3:0] A,
    input logic [1:0] shift_amount,
    input logic shift_dir,
    input logic enable,
    input logic [1:0] select,
    output logic [15:0] out
);
    // Barrel shifter properties
    // Left shift by 0 should not change A
    left_shift_0: assert property (
        @(posedge clk) disable iff (!rst_n) (shift_dir && shift_amount == 2'b00) |-> (out[3:0] == A)
    );
    // Right shift by 0 should not change A
    right_shift_0: assert property (
        @(posedge clk) disable iff (!rst_n) (!shift_dir && shift_amount == 2'b00) |-> (out[3:0] == A)
    );
    // Barrel shifter output should be within valid range
    barrel_shifter_output_range: assert property (
        @(posedge clk) disable iff (!rst_n) (out[3:0] >= 4'b0000 && out[3:0] <= 4'b1111)
    );

    // Decoder properties
    // Decoder output should be within valid range when enabled
    decoder_output_range: assert property (
        @(posedge clk) disable iff (!rst_n) (enable |-> (out[15:4] >= 12'h0000 && out[15:4] <= 12'h000F))
    );
    // Decoder output should be 0 when disabled
    decoder_output_zero: assert property (
        @(posedge clk) disable iff (!rst_n) (!enable |-> (out[15:4] == 12'h0000))
    );

    // Top module properties
    // Output should be correct when both barrel shifter and decoder are active
    top_module_output_correct: assert property (
        @(posedge clk) disable iff (!rst_n) (enable && shift_dir && shift_amount == 2'b00) |-> (out == {16'b0, A})
    );
    // Output should be correct when both barrel shifter and decoder are active
    top_module_output_correct_2: assert property (
        @(posedge clk) disable iff (!rst_n) (enable && !shift_dir && shift_amount == 2'b00) |-> (out == {16'b0, A})
    );
    // Output should be correct when both barrel shifter and decoder are active
    top_module_output_correct_3: assert property (
        @(posedge clk) disable iff (!rst_n) (enable && shift_dir && shift_amount == 2'b01) |-> (out == {16'b0, {A[2:0], 1'b0}})
    );
    // Output should be correct when both barrel shifter and decoder are active
    top_module_output_correct_4: assert property (
        @(posedge clk) disable iff (!rst_n) (enable && !shift_dir && shift_amount == 2'b01) |-> (out == {16'b0, {1'b0, A[3:1]}})
    );
    // Output should be correct when both barrel shifter and decoder are active
    top_module_output_correct_5: assert property (
        @(posedge clk) disable iff (!rst_n) (enable && shift_dir && shift_amount == 2'b10) |-> (out == {16'b0, {A[1:0], 2'b00}})
    );
    // Output should be correct when both barrel shifter and decoder are active
    top_module_output_correct_6: assert property (
        @(posedge clk) disable iff (!rst_n) (enable && !shift_dir && shift_amount == 2'b10) |-> (out == {16'b0, {2'b00, A[3:2]}})
    );
    // Output should be correct when both barrel shifter and decoder are active
    top_module_output_correct_7: assert property (
        @(posedge clk) disable iff (!rst_n) (enable && shift_dir && shift_amount == 2'b11) |-> (out == {16'b0, {A[0], 3'b000}})
    );
    // Output should be correct when both barrel shifter and decoder are active
    top_module_output_correct_8: assert property (
        @(posedge clk) disable iff (!rst_n) (enable && !shift_dir && shift_amount == 2'b11) |-> (out == {16'b0, {3'b000, A[3]}})
    );
endmodule