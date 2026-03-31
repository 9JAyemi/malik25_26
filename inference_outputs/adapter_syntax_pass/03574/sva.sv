module square_module_sva (
    input logic [3:0] num,
    input logic [7:0] square
);

    // Square must equal the 4-bit input value squared.
    check_square_matches_input: assert property (
        @($global_clock) square == (num * num)
    );

    // Zero input must produce zero output.
    check_zero_input_zero_output: assert property (
        @($global_clock) (num == 4'd0) |-> (square == 8'd0)
    );

    // One input must produce one output.
    check_one_input_one_output: assert property (
        @($global_clock) (num == 4'd1) |-> (square == 8'd1)
    );

    // Four input must produce sixteen output.
    check_four_input_sixteen_output: assert property (
        @($global_clock) (num == 4'd4) |-> (square == 8'd16)
    );

    // Five input must produce twenty-five output.
    check_five_input_twentyfive_output: assert property (
        @($global_clock) (num == 4'd5) |-> (square == 8'd25)
    );

    // Eight input must produce sixty-four output.
    check_eight_input_sixtyfour_output: assert property (
        @($global_clock) (num == 4'd8) |-> (square == 8'd64)
    );

    // Nine input must produce eighty-one output.
    check_nine_input_eightyone_output: assert property (
        @($global_clock) (num == 4'd9) |-> (square == 8'd81)
    );

    // Maximum input must produce 15^2 = 225 output.
    check_max_input_square: assert property (
        @($global_clock) (num == 4'hF) |-> (square == 8'd225)
    );

endmodule