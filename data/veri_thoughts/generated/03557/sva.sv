module barrel_shifter_sva (
    input logic       clk,
    input logic [3:0] data_in,
    input logic [1:0] shift_amount,
    input logic       mode,
    input logic [3:0] data_out
);

    // mode=0 selects the reachable left-shift case item.
    check_mode0_left_shift: assert property (
        @(posedge clk)
        (mode === 1'b0) |-> (data_out === (data_in << shift_amount))
    );

    // mode=1 selects the reachable right-shift case item.
    check_mode1_right_shift: assert property (
        @(posedge clk)
        (mode === 1'b1) |-> (data_out === (data_in >> shift_amount))
    );

    // mode=0 with shift_amount=0 leaves the input unchanged.
    check_left_shift_0: assert property (
        @(posedge clk)
        (mode === 1'b0 && shift_amount === 2'd0) |-> (data_out === data_in)
    );

    // mode=0 with shift_amount=1 shifts left by one bit.
    check_left_shift_1: assert property (
        @(posedge clk)
        (mode === 1'b0 && shift_amount === 2'd1) |-> (data_out === {data_in[2:0], 1'b0})
    );

    // mode=0 with shift_amount=2 shifts left by two bits.
    check_left_shift_2: assert property (
        @(posedge clk)
        (mode === 1'b0 && shift_amount === 2'd2) |-> (data_out === {data_in[1:0], 2'b00})
    );

    // mode=0 with shift_amount=3 shifts left by three bits.
    check_left_shift_3: assert property (
        @(posedge clk)
        (mode === 1'b0 && shift_amount === 2'd3) |-> (data_out === {data_in[0], 3'b000})
    );

    // mode=1 with shift_amount=0 leaves the input unchanged.
    check_right_shift_0: assert property (
        @(posedge clk)
        (mode === 1'b1 && shift_amount === 2'd0) |-> (data_out === data_in)
    );

    // mode=1 with shift_amount=1 shifts right by one bit.
    check_right_shift_1: assert property (
        @(posedge clk)
        (mode === 1'b1 && shift_amount === 2'd1) |-> (data_out === {1'b0, data_in[3:1]})
    );

    // mode=1 with shift_amount=2 shifts right by two bits.
    check_right_shift_2: assert property (
        @(posedge clk)
        (mode === 1'b1 && shift_amount === 2'd2) |-> (data_out === {2'b00, data_in[3:2]})
    );

    // mode=1 with shift_amount=3 shifts right by three bits.
    check_right_shift_3: assert property (
        @(posedge clk)
        (mode === 1'b1 && shift_amount === 2'd3) |-> (data_out === {3'b000, data_in[3]})
    );

endmodule