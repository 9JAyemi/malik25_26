module barrel_shifter_sva (
    input logic [7:0] data_in,
    input logic [2:0] shift_amount,
    input logic [7:0] data_out
);

    // 000 passes data_in through.
    check_shift_000_passthrough: assert property (
        @($global_clock) (shift_amount === 3'b000) |-> (data_out === data_in)
    );

    // 001 shifts right by one with sign extension.
    check_shift_001_arith_right_1: assert property (
        @($global_clock) (shift_amount === 3'b001) |-> (data_out === {data_in[7], data_in[7:1]})
    );

    // 010 shifts left by two with zero fill.
    check_shift_010_left_2: assert property (
        @($global_clock) (shift_amount === 3'b010) |-> (data_out === {data_in[5:0], 2'b00})
    );

    // 011 shifts left by three with zero fill.
    check_shift_011_left_3: assert property (
        @($global_clock) (shift_amount === 3'b011) |-> (data_out === {data_in[4:0], 3'b000})
    );

    // 100 shifts left by four with zero fill.
    check_shift_100_left_4: assert property (
        @($global_clock) (shift_amount === 3'b100) |-> (data_out === {data_in[3:0], 4'b0000})
    );

    // 101 shifts left by five with zero fill.
    check_shift_101_left_5: assert property (
        @($global_clock) (shift_amount === 3'b101) |-> (data_out === {data_in[2:0], 5'b00000})
    );

    // 110 shifts left by six with zero fill.
    check_shift_110_left_6: assert property (
        @($global_clock) (shift_amount === 3'b110) |-> (data_out === {data_in[1:0], 6'b000000})
    );

    // 111 shifts left by seven with zero fill.
    check_shift_111_left_7: assert property (
        @($global_clock) (shift_amount === 3'b111) |-> (data_out === {data_in[0], 7'b0000000})
    );

endmodule