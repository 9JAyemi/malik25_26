module jt51_lin2exp_sva (
    input logic        clk,
    input logic [15:0] lin,
    input logic [9:0]  man,
    input logic [2:0]  exp
);

    // Prefix 10 or 01 maps to exp 7 and lin[15:6].
    check_exp7_class: assert property (
        @(posedge clk)
        (((lin[15:14] == 2'b10) || (lin[15:14] == 2'b01)) |-> ((man == lin[15:6]) && (exp == 3'd7)))
    );

    // Prefix 110 or 001 maps to exp 6 and lin[14:5].
    check_exp6_class: assert property (
        @(posedge clk)
        (((lin[15:13] == 3'b110) || (lin[15:13] == 3'b001)) |-> ((man == lin[14:5]) && (exp == 3'd6)))
    );

    // Prefix 1110 or 0001 maps to exp 5 and lin[13:4].
    check_exp5_class: assert property (
        @(posedge clk)
        (((lin[15:12] == 4'b1110) || (lin[15:12] == 4'b0001)) |-> ((man == lin[13:4]) && (exp == 3'd5)))
    );

    // Prefix 11110 or 00001 maps to exp 4 and lin[12:3].
    check_exp4_class: assert property (
        @(posedge clk)
        (((lin[15:11] == 5'b11110) || (lin[15:11] == 5'b00001)) |-> ((man == lin[12:3]) && (exp == 3'd4)))
    );

    // Prefix 111110 or 000001 maps to exp 3 and lin[11:2].
    check_exp3_class: assert property (
        @(posedge clk)
        (((lin[15:10] == 6'b111110) || (lin[15:10] == 6'b000001)) |-> ((man == lin[11:2]) && (exp == 3'd3)))
    );

    // Prefix 1111110 or 0000001 maps to exp 2 and lin[10:1].
    check_exp2_class: assert property (
        @(posedge clk)
        (((lin[15:9] == 7'b1111110) || (lin[15:9] == 7'b0000001)) |-> ((man == lin[10:1]) && (exp == 3'd2)))
    );

    // Prefix 1111111 or 0000000 maps to exp 1 and lin[9:0].
    check_exp1_class: assert property (
        @(posedge clk)
        (((lin[15:9] == 7'b1111111) || (lin[15:9] == 7'b0000000)) |-> ((man == lin[9:0]) && (exp == 3'd1)))
    );

    // The outputs must match one of the seven implemented prefix classes.
    check_complete_mapping: assert property (
        @(posedge clk)
        (
            ((((lin[15:14] == 2'b10) || (lin[15:14] == 2'b01)) && (man == lin[15:6]) && (exp == 3'd7))) ||
            ((((lin[15:13] == 3'b110) || (lin[15:13] == 3'b001)) && (man == lin[14:5]) && (exp == 3'd6))) ||
            ((((lin[15:12] == 4'b1110) || (lin[15:12] == 4'b0001)) && (man == lin[13:4]) && (exp == 3'd5))) ||
            ((((lin[15:11] == 5'b11110) || (lin[15:11] == 5'b00001)) && (man == lin[12:3]) && (exp == 3'd4))) ||
            ((((lin[15:10] == 6'b111110) || (lin[15:10] == 6'b000001)) && (man == lin[11:2]) && (exp == 3'd3))) ||
            ((((lin[15:9]  == 7'b1111110) || (lin[15:9]  == 7'b0000001)) && (man == lin[10:1]) && (exp == 3'd2))) ||
            ((((lin[15:9]  == 7'b1111111) || (lin[15:9]  == 7'b0000000)) && (man == lin[9:0])  && (exp == 3'd1)))
        )
    );

    // The exponent is never driven to zero.
    check_exp_nonzero: assert property (
        @(posedge clk)
        (exp != 3'd0)
    );

    // If the input is unchanged, the sampled outputs remain unchanged.
    check_outputs_stable_when_input_stable: assert property (
        @(posedge clk)
        $stable(lin) |-> $stable({man, exp})
    );

endmodule