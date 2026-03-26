module Barrel_Shifter_sva (
    input logic        clk,
    input logic        rst,
    input logic        load_i,
    input logic [31:0] Shift_Value_i,
    input logic [31:0] Shift_Data_i,
    input logic        Left_Right_i,
    input logic        Bit_Shift_i,
    input logic [31:0] N_mant_o
);

    // Synchronous reset drives the output to zero.
    check_reset_clears_output: assert property (
        @(posedge clk) rst |=> (N_mant_o == 32'b0)
    );

    // Without a load, the output holds its previous value.
    check_hold_when_not_loading: assert property (
        @(posedge clk) disable iff (rst)
        (!load_i) |=> (N_mant_o == $past(N_mant_o))
    );

    // Full-width left shift is used when load, bit-shift, and left are selected.
    check_full_left_shift: assert property (
        @(posedge clk) disable iff (rst)
        (load_i && Bit_Shift_i && Left_Right_i) |=> (N_mant_o == ($past(Shift_Data_i) << $past(Shift_Value_i)))
    );

    // Full-width right shift is used when load, bit-shift, and right are selected.
    check_full_right_shift: assert property (
        @(posedge clk) disable iff (rst)
        (load_i && Bit_Shift_i && !Left_Right_i) |=> (N_mant_o == ($past(Shift_Data_i) >> $past(Shift_Value_i)))
    );

    // Modulo-32 left shift is used when load, modulo mode, and left are selected.
    check_modulo_left_shift: assert property (
        @(posedge clk) disable iff (rst)
        (load_i && !Bit_Shift_i && Left_Right_i) |=> (N_mant_o == ($past(Shift_Data_i) << ($past(Shift_Value_i) % 32)))
    );

    // Modulo-32 right shift is used when load, modulo mode, and right are selected.
    check_modulo_right_shift: assert property (
        @(posedge clk) disable iff (rst)
        (load_i && !Bit_Shift_i && !Left_Right_i) |=> (N_mant_o == ($past(Shift_Data_i) >> ($past(Shift_Value_i) % 32)))
    );

endmodule