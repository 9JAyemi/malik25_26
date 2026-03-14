module shift_reg_4bit_sva (
    input logic clk,
    input logic shift_parallel,
    input logic [3:0] parallel_in,
    input logic [3:0] out
);

    // When shifting, next out equals previous out<<1 with 0 inserted at LSB.
    check_shift_nextval: assert property (
        @(posedge clk) shift_parallel |=> out == { $past(out)[2:0], 1'b0 }
    );

    // When shifting, next LSB is 0.
    check_shift_lsb_zero: assert property (
        @(posedge clk) shift_parallel |=> out[0] == 1'b0
    );

    // When shifting, next [3:1] equals previous [2:0].
    check_shift_upper_bits_move: assert property (
        @(posedge clk) shift_parallel |=> out[3:1] == $past(out[2:0])
    );

    // When not shifting, next out equals previous parallel_in.
    check_parallel_load: assert property (
        @(posedge clk) !shift_parallel |=> out == $past(parallel_in)
    );

    // When not shifting, next MSB equals previous parallel_in[3].
    check_parallel_load_msb: assert property (
        @(posedge clk) !shift_parallel |=> out[3] == $past(parallel_in[3])
    );

    // When not shifting, next LSB equals previous parallel_in[0].
    check_parallel_load_lsb: assert property (
        @(posedge clk) !shift_parallel |=> out[0] == $past(parallel_in[0])
    );

    // Two consecutive shifts are equivalent to left shift by 2 with zeros.
    check_two_consecutive_shifts: assert property (
        @(posedge clk) (shift_parallel ##1 shift_parallel) |=> out == { $past(out,2)[1:0], 2'b00 }
    );

    // Four consecutive shifts clear the register to zero.
    check_four_shifts_zero: assert property (
        @(posedge clk) shift_parallel[*4] |=> out == 4'b0000
    );

endmodule