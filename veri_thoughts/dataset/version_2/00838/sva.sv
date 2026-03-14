module barrel_shifter_sva (
    input logic CLK,
    input logic [3:0] data,
    input logic [1:0] shift_amount,
    input logic [3:0] result
);
    // Result matches the full case-defined function for all shift_amount values.
    check_function_complete: assert property (
        @(posedge CLK)
            ((shift_amount == 2'b00) && (result == data)) ||
            ((shift_amount == 2'b01) && (result == {data[2:0], 1'b0})) ||
            ((shift_amount == 2'b10) && (result == {data[1:0], 2'b00})) ||
            ((shift_amount == 2'b11) && (result == 4'b0000))
    );

    // No shift: result equals data when shift_amount == 2'b00.
    check_no_shift_passthrough: assert property (
        @(posedge CLK) (shift_amount == 2'b00) |-> (result == data)
    );

    // Shift by 1: result equals {data[2:0], 1'b0} when shift_amount == 2'b01.
    check_shift1_concat: assert property (
        @(posedge CLK) (shift_amount == 2'b01) |-> (result == {data[2:0], 1'b0})
    );

    // Shift by 2: result equals {data[1:0], 2'b00} when shift_amount == 2'b10.
    check_shift2_concat: assert property (
        @(posedge CLK) (shift_amount == 2'b10) |-> (result == {data[1:0], 2'b00})
    );

    // Shift by 3 (2'b11): result is 4'b0000 regardless of data.
    check_shift3_zero: assert property (
        @(posedge CLK) (shift_amount == 2'b11) |-> (result == 4'b0000)
    );

    // Shift by 1: LSB is forced to 0.
    check_shift1_lsb_zero: assert property (
        @(posedge CLK) (shift_amount == 2'b01) |-> (result[0] == 1'b0)
    );

    // Shift by 2: two LSBs are forced to 0.
    check_shift2_lsbs_zero: assert property (
        @(posedge CLK) (shift_amount == 2'b10) |-> (result[1:0] == 2'b00)
    );

    // Shift by 1: upper bits map to data[2:0].
    check_shift1_upper_map: assert property (
        @(posedge CLK) (shift_amount == 2'b01) |-> (result[3:1] == data[2:0])
    );

    // Shift by 2: upper two bits map to data[1:0].
    check_shift2_upper_map: assert property (
        @(posedge CLK) (shift_amount == 2'b10) |-> (result[3:2] == data[1:0])
    );

    // Purely combinational behavior: if inputs are stable, result is stable.
    check_stability_with_stable_inputs: assert property (
        @(posedge CLK) ($stable(data) && $stable(shift_amount)) |-> $stable(result)
    );
endmodule