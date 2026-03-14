module BitwiseLeftShift_sva (
    input logic clk,
    input logic [7:0] data_in,
    input logic [2:0] shift_amount,
    input logic [7:0] data_out
);
    // Output equals data_in left-shifted by shift_amount.
    check_output_matches_shift: assert property (
        @(posedge clk) (data_out == (data_in << shift_amount))
    );

    // Shift by 0 leaves output unchanged.
    check_shift_by_zero_identity: assert property (
        @(posedge clk) (shift_amount == 3'd0) |=> (data_out == data_in)
    );

    // Shift by 1 inserts one trailing zero.
    check_shift_by_one: assert property (
        @(posedge clk) (shift_amount == 3'd1) |=> (data_out == {data_in[6:0], 1'b0})
    );

    // Shift by 2 inserts two trailing zeros.
    check_shift_by_two: assert property (
        @(posedge clk) (shift_amount == 3'd2) |=> (data_out == {data_in[5:0], 2'b00})
    );

    // Shift by 3 inserts three trailing zeros.
    check_shift_by_three: assert property (
        @(posedge clk) (shift_amount == 3'd3) |=> (data_out == {data_in[4:0], 3'b000})
    );

    // Shift by 4 inserts four trailing zeros.
    check_shift_by_four: assert property (
        @(posedge clk) (shift_amount == 3'd4) |=> (data_out == {data_in[3:0], 4'b0000})
    );

    // Shift by 5 inserts five trailing zeros.
    check_shift_by_five: assert property (
        @(posedge clk) (shift_amount == 3'd5) |=> (data_out == {data_in[2:0], 5'b0_0000})
    );

    // Shift by 6 inserts six trailing zeros.
    check_shift_by_six: assert property (
        @(posedge clk) (shift_amount == 3'd6) |=> (data_out == {data_in[1:0], 6'b00_0000})
    );

    // Shift by 7 inserts seven trailing zeros.
    check_shift_by_seven: assert property (
        @(posedge clk) (shift_amount == 3'd7) |=> (data_out == {data_in[0], 7'b0_000000})
    );

    // Zero input always produces zero output.
    check_zero_input_zero_output: assert property (
        @(posedge clk) (data_in == 8'b0) |=> (data_out == 8'b0)
    );
endmodule