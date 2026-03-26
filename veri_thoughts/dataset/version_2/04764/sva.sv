module byte_order_adder_sva (
    input logic        clk,
    input logic        reset,
    input logic [31:0] data_in1,
    input logic [31:0] data_in2,
    input logic [31:0] sum_out
);

    function automatic logic [31:0] swap32(input logic [31:0] value);
        begin
            swap32 = {value[7:0], value[15:8], value[23:16], value[31:24]};
        end
    endfunction

    // Reset clears the registered sum, so the output is zero on the next cycle.
    check_reset_clears_output: assert property (
        @(posedge clk) reset |=> (sum_out == 32'h00000000)
    );

    // The output reflects the previous cycle's byte-reversed input sum after one clock.
    check_output_matches_registered_byte_reversed_sum: assert property (
        @(posedge clk) disable iff (reset || $isunknown($past(reset)))
        (1'b1 |=> (sum_out == swap32(swap32($past(data_in1)) + swap32($past(data_in2)))))
    );

    // With data_in2 at zero, the byte swaps cancel and data_in1 passes through in one cycle.
    check_data_in1_passthrough_when_data_in2_zero: assert property (
        @(posedge clk) disable iff (reset || $isunknown($past(reset)))
        ((data_in2 == 32'h00000000) |=> (sum_out == $past(data_in1)))
    );

    // With data_in1 at zero, the byte swaps cancel and data_in2 passes through in one cycle.
    check_data_in2_passthrough_when_data_in1_zero: assert property (
        @(posedge clk) disable iff (reset || $isunknown($past(reset)))
        ((data_in1 == 32'h00000000) |=> (sum_out == $past(data_in2)))
    );

    // When both inputs are zero, the output is zero in the next cycle.
    check_zero_inputs_produce_zero_output: assert property (
        @(posedge clk) disable iff (reset || $isunknown($past(reset)))
        (((data_in1 == 32'h00000000) && (data_in2 == 32'h00000000)) |=> (sum_out == 32'h00000000))
    );

endmodule