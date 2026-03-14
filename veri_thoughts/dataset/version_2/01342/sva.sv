module subtract5_sva (
    input  logic [3:0] input_num,
    input  logic [3:0] output_num
);

    // For this combinational DUT with no clock/reset, sample on posedge of input_num[0].

    // If input <= 5, output equals 5 - input.
    check_subtract_when_le5: assert property (
        @(posedge input_num[0]) (input_num <= 4'd5) |-> (output_num == (4'd5 - input_num))
    );

    // If input > 5, output is zero (saturates at 0).
    check_saturate_when_gt5: assert property (
        @(posedge input_num[0]) (input_num > 4'd5) |-> (output_num == 4'd0)
    );

    // Output is always in range 0..5.
    check_output_range_to_five: assert property (
        @(posedge input_num[0]) (output_num <= 4'd5)
    );

    // Output zero implies input is >= 5.
    check_zero_output_implies_ge5: assert property (
        @(posedge input_num[0]) (output_num == 4'd0) |-> (input_num >= 4'd5)
    );

    // For input <= 5, output + input == 5.
    check_sum_is_five_when_input_le5: assert property (
        @(posedge input_num[0]) (input_num <= 4'd5) |-> ((output_num + input_num) == 4'd5)
    );

    // Bit[3] of output is always zero (output never exceeds 5).
    check_output_bit3_is_zero: assert property (
        @(posedge input_num[0]) (output_num[3] == 1'b0)
    );

    // Input 0 maps to output 5.
    check_case_input0_output5: assert property (
        @(posedge input_num[0]) (input_num == 4'd0) |-> (output_num == 4'd5)
    );

    // Input 5 maps to output 0.
    check_case_input5_output0: assert property (
        @(posedge input_num[0]) (input_num == 4'd5) |-> (output_num == 4'd0)
    );

    // If input is stable across samples, output is stable (pure combinational mapping).
    check_output_stable_when_input_stable: assert property (
        @(posedge input_num[0]) ($past(1'b1) && (input_num == $past(input_num))) |-> (output_num == $past(output_num))
    );

    // If input increments by 1 within 0..5, output decrements by 1 (until saturation).
    check_output_decrements_on_input_increment: assert property (
        @(posedge input_num[0])
            ($past(1'b1) && ($past(input_num) <= 4'd4) && (input_num == ($past(input_num) + 1)))
            |-> (output_num == ($past(output_num) - 1))
    );

endmodule