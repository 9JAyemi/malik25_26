module shift_register_sva (
    input logic clk,
    input logic load,
    input logic [3:0] data_in,
    output logic [3:0] data_out
);
    // Sequential logic: shift_reg is updated on the rising edge of clk
    // Shift register should update to data_in when load is asserted
    shift_on_load: assert property (
        @(posedge clk) disable iff (!load) shift_reg == data_in
    );

    // Sequential logic: shift_reg is updated on the rising edge of clk
    // Shift register should shift left by one bit when load is not asserted
    shift_on_not_load: assert property (
        @(posedge clk) disable iff (!load) shift_reg == {shift_reg[2:0], 1'b0}
    );

    // Sequential logic: shift_reg is updated on the rising edge of clk
    // Shift register should not change when load is not asserted
    no_change_on_not_load: assert property (
        @(posedge clk) disable iff (!load) shift_reg == shift_reg
    );

    // Combinational logic: data_out is assigned the value of shift_reg
    // data_out should always be equal to shift_reg
    data_out_assignment: assert property (
        @(posedge clk) data_out == shift_reg
    );

    // Sequential logic: shift_reg is updated on the rising edge of clk
    // Shift register should not be affected by the reset signal
    shift_reg_no_reset: assert property (
        @(posedge clk) disable iff (!load) shift_reg != 4'b0000
    );

    // Sequential logic: shift_reg is updated on the rising edge of clk
    // Shift register should not be affected by the reset signal
    shift_reg_no_reset_2: assert property (
        @(posedge clk) disable iff (!load) shift_reg != 4'b1111
    );

    // Sequential logic: shift_reg is updated on the rising edge of clk
    // Shift register should not be affected by the reset signal
    shift_reg_no_reset_3: assert property (
        @(posedge clk) disable iff (!load) shift_reg != 4'b1010
    );

    // Sequential logic: shift_reg is updated on the rising edge of clk
    // Shift register should not be affected by the reset signal
    shift_reg_no_reset_4: assert property (
        @(posedge clk) disable iff (!load) shift_reg != 4'b0101
    );

    // Sequential logic: shift_reg is updated on the rising edge of clk
    // Shift register should not be affected by the reset signal
    shift_reg_no_reset_5: assert property (
        @(posedge clk) disable iff (!load) shift_reg != 4'b0011
    );

    // Sequential logic: shift_reg is updated on the rising edge of clk
    // Shift register should not be affected by the reset signal
    shift_reg_no_reset_6: assert property (
        @(posedge clk) disable iff (!load) shift_reg != 4'b1100
    );

    // Sequential logic: shift_reg is updated on the rising edge of clk
    // Shift register should not be affected by the reset signal
    shift_reg_no_reset_7: assert property (
        @(posedge clk) disable iff (!load) shift_reg != 4'b1001
    );

    // Sequential logic: shift_reg is updated on the rising edge of clk
    // Shift register should not be affected by the reset signal
    shift_reg_no_reset_8: assert property (
        @(posedge clk) disable iff (!load) shift_reg != 4'b0110
    );
endmodule