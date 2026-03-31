module barrel_shifter_sva (
    input logic CLK,          // Added sampling clock for SVA (RTL has no clock/reset)
    input logic [15:0] in,
    input logic [3:0]  shift,
    input logic        dir,
    input logic [15:0] out
);
    // Left shift definition: dir==0 makes out = in << shift.
    check_left_shift_definition: assert property (
        @(posedge CLK) (dir == 1'b0) |-> (out == (in << shift))
    );

    // Right shift definition: dir==1 makes out = in >> shift.
    check_right_shift_definition: assert property (
        @(posedge CLK) (dir == 1'b1) |-> (out == (in >> shift))
    );

    // Zero shift is identity regardless of dir.
    check_shift_zero_identity: assert property (
        @(posedge CLK) (shift == 4'd0) |-> (out == in)
    );

    // Zero input yields zero output for any dir/shift.
    check_zero_input_zero_output: assert property (
        @(posedge CLK) (in == 16'h0000) |-> (out == 16'h0000)
    );

    // Left shift zero-fill: lower 'shift' bits of out are zero.
    check_left_zero_fill_lowbits: assert property (
        @(posedge CLK) (dir == 1'b0) |-> ((out & (((16'h0001 << shift) - 16'h0001))) == 16'h0000)
    );

    // Right shift zero-fill: upper 'shift' bits of out are zero.
    check_right_zero_fill_highbits: assert property (
        @(posedge CLK) (dir == 1'b1) |-> ((out & (16'hFFFF << (16 - shift))) == 16'h0000)
    );

    // Left shift by 15: out[14:0]==0 and out[15]==in[0].
    check_left_shift_by_15_detail: assert property (
        @(posedge CLK) ((dir == 1'b0) && (shift == 4'd15)) |-> ((out[14:0] == 15'b0) && (out[15] == in[0]))
    );

    // Right shift by 15: out[15:1]==0 and out[0]==in[15].
    check_right_shift_by_15_detail: assert property (
        @(posedge CLK) ((dir == 1'b1) && (shift == 4'd15)) |-> ((out[15:1] == 15'b0) && (out[0] == in[15]))
    );

    // Left shift by 1: LSB zero and remaining bits align with in.
    check_left_shift_by_1_detail: assert property (
        @(posedge CLK) ((dir == 1'b0) && (shift == 4'd1)) |-> ((out[0] == 1'b0) && (out[15:1] == in[14:0]))
    );

    // Right shift by 1: MSB zero and remaining bits align with in.
    check_right_shift_by_1_detail: assert property (
        @(posedge CLK) ((dir == 1'b1) && (shift == 4'd1)) |-> ((out[15] == 1'b0) && (out[14:0] == in[15:1]))
    );
endmodule