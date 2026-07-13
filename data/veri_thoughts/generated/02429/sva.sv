module barrel_shifter_sva (
    input logic CLK,
    input logic RESETn,
    input logic [3:0] in,
    input logic [1:0] control,
    input logic [3:0] out
);
    // For control 00, output equals input shifted left by 1.
    check_left_shift1_eq: assert property (
        @(posedge CLK) disable iff (!RESETn) (control == 2'b00) |-> (out == (in << 1))
    );
    // For control 01, output equals input shifted left by 2.
    check_left_shift2_eq: assert property (
        @(posedge CLK) disable iff (!RESETn) (control == 2'b01) |-> (out == (in << 2))
    );
    // For control 10, output equals input shifted right by 1.
    check_right_shift1_eq: assert property (
        @(posedge CLK) disable iff (!RESETn) (control == 2'b10) |-> (out == (in >> 1))
    );
    // For control 11, output equals input shifted right by 2.
    check_right_shift2_eq: assert property (
        @(posedge CLK) disable iff (!RESETn) (control == 2'b11) |-> (out == (in >> 2))
    );

    // For left shift by 1, LSB is zero.
    check_left1_lsb_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) (control == 2'b00) |-> (out[0] == 1'b0)
    );
    // For left shift by 2, two LSBs are zero.
    check_left2_lsbs_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) (control == 2'b01) |-> (out[1:0] == 2'b00)
    );
    // For right shift by 1, MSB is zero.
    check_right1_msb_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) (control == 2'b10) |-> (out[3] == 1'b0)
    );
    // For right shift by 2, two MSBs are zero.
    check_right2_msbs_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) (control == 2'b11) |-> (out[3:2] == 2'b00)
    );

    // For left shift by 1, upper bits map to input [2:0].
    check_left1_bit_mapping: assert property (
        @(posedge CLK) disable iff (!RESETn) (control == 2'b00) |-> (out[3:1] == in[2:0])
    );
    // For right shift by 1, lower bits map to input [3:1].
    check_right1_bit_mapping: assert property (
        @(posedge CLK) disable iff (!RESETn) (control == 2'b10) |-> (out[2:0] == in[3:1])
    );
endmodule