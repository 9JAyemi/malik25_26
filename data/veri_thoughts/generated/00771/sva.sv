module barrel_shifter_16bit_sva (
    input logic clk,
    input logic [15:0] data,
    input logic [3:0] shift_amount,
    input logic [15:0] out
);
    ///// Functional mapping for each shift combination (shift_amount[3:1]) /////
    // No shift when [3:1]==000.
    check_shift_0: assert property (
        @(posedge clk) (shift_amount[3:1] == 3'b000) |-> (out == data)
    );

    // Shift by 2 when [3:1]==001.
    check_shift_2: assert property (
        @(posedge clk) (shift_amount[3:1] == 3'b001) |-> (out == (data << 2))
    );

    // Shift by 4 when [3:1]==010.
    check_shift_4: assert property (
        @(posedge clk) (shift_amount[3:1] == 3'b010) |-> (out == (data << 4))
    );

    // Shift by 6 when [3:1]==011.
    check_shift_6: assert property (
        @(posedge clk) (shift_amount[3:1] == 3'b011) |-> (out == (data << 6))
    );

    // Shift by 8 when [3:1]==100.
    check_shift_8: assert property (
        @(posedge clk) (shift_amount[3:1] == 3'b100) |-> (out == (data << 8))
    );

    // Shift by 10 when [3:1]==101.
    check_shift_10: assert property (
        @(posedge clk) (shift_amount[3:1] == 3'b101) |-> (out == (data << 10))
    );

    // Shift by 12 when [3:1]==110.
    check_shift_12: assert property (
        @(posedge clk) (shift_amount[3:1] == 3'b110) |-> (out == (data << 12))
    );

    // Shift by 14 when [3:1]==111.
    check_shift_14: assert property (
        @(posedge clk) (shift_amount[3:1] == 3'b111) |-> (out == (data << 14))
    );

    ///// Bit-level structural consequences of left shifts /////
    // LSBs [1:0] are zeroed whenever shift by 2 is selected.
    check_lsb_zero_when_b1: assert property (
        @(posedge clk) shift_amount[1] |-> (out[1:0] == 2'b00)
    );

    // LSBs [3:0] are zeroed whenever shift by 4 is selected.
    check_lsb_zero_when_b2: assert property (
        @(posedge clk) shift_amount[2] |-> (out[3:0] == 4'b0000)
    );

    // LSBs [7:0] are zeroed whenever shift by 8 is selected.
    check_lsb_zero_when_b3: assert property (
        @(posedge clk) shift_amount[3] |-> (out[7:0] == 8'b0000_0000)
    );

    ///// Insensitivity to shift_amount[0] /////
    // Changing shift_amount[0] alone does not change out.
    check_ignore_shift_bit0: assert property (
        @(posedge clk) ($changed(shift_amount[0]) && $stable(data) && $stable(shift_amount[3:1])) |-> $stable(out)
    );

    ///// Combinational stability /////
    // If inputs are stable, output stays stable.
    check_stable_inputs_imply_stable_out: assert property (
        @(posedge clk) ($stable(data) && $stable(shift_amount)) |-> $stable(out)
    );
endmodule