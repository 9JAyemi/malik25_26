module shift_register_sva (
    input logic clk,
    input logic serial_in,
    input logic serial_out,
    input logic [2:0] shift_reg,
    input logic [1:0] mux_sel,
    input logic d1,
    input logic d2,
    input logic d3
);
    ///// Continuous assign consistency /////
    // d1 must always mirror serial_in.
    check_d1_maps_serial_in: assert property (
        @(posedge clk) disable iff ($initstate) d1 == serial_in
    );
    // d2 must always mirror shift_reg[0].
    check_d2_maps_shift_reg0: assert property (
        @(posedge clk) disable iff ($initstate) d2 == shift_reg[0]
    );
    // d3 must always mirror shift_reg[1].
    check_d3_maps_shift_reg1: assert property (
        @(posedge clk) disable iff ($initstate) d3 == shift_reg[1]
    );

    ///// Shift register update /////
    // On each clk, shift_reg loads {prev shift_reg[1], prev shift_reg[0], prev serial_in}.
    check_shift_reg_update_concat: assert property (
        @(posedge clk) disable iff ($initstate) shift_reg == { $past(shift_reg[1]), $past(shift_reg[0]), $past(serial_in) }
    );
    // MSB shifts from previous bit1.
    check_sr2_from_sr1: assert property (
        @(posedge clk) disable iff ($initstate) shift_reg[2] == $past(shift_reg[1])
    );
    // Mid bit shifts from previous bit0.
    check_sr1_from_sr0: assert property (
        @(posedge clk) disable iff ($initstate) shift_reg[1] == $past(shift_reg[0])
    );
    // LSB captures previous serial_in.
    check_sr0_from_si: assert property (
        @(posedge clk) disable iff ($initstate) shift_reg[0] == $past(serial_in)
    );

    ///// Muxed serial_out behavior /////
    // When mux_sel==00, serial_out equals d1.
    check_out_sel_d1: assert property (
        @(posedge clk) disable iff ($initstate) (mux_sel == 2'b00) |-> (serial_out == d1)
    );
    // When mux_sel==01, serial_out equals d2.
    check_out_sel_d2: assert property (
        @(posedge clk) disable iff ($initstate) (mux_sel == 2'b01) |-> (serial_out == d2)
    );
    // When mux_sel==10, serial_out equals d3.
    check_out_sel_d3: assert property (
        @(posedge clk) disable iff ($initstate) (mux_sel == 2'b10) |-> (serial_out == d3)
    );
endmodule