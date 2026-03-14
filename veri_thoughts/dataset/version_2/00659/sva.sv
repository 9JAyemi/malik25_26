module rotator_mux_sva (
    input logic clk,
    input logic load,
    input logic [1:0] ena,
    input logic [99:0] data,
    input logic [2:0] sel, 
    input logic [3:0] data0,
    input logic [3:0] data1,
    input logic [3:0] data2,
    input logic [3:0] data3,
    input logic [3:0] data4,
    input logic [3:0] data5,
    input logic [7:0] out,
    input logic [99:0] shift_reg
);
    // Clock: clk (posedge). No reset in RTL.

    ///// Shift register behavior /////
    // Loading has priority and captures data on next clock.
    check_shift_loads_data: assert property (
        @(posedge clk) load |=> (shift_reg == $past(data))
    );

    // With ena[0]=1 and no load, rotate left by 1 on next clock.
    check_shift_left_when_ena0: assert property (
        @(posedge clk) (!load && ena[0]) |=> (shift_reg == { $past(shift_reg[98:0]), $past(shift_reg[99]) })
    );

    // With ena[1]=1, ena[0]=0, and no load, rotate right by 1 on next clock.
    check_shift_right_when_ena1: assert property (
        @(posedge clk) (!load && !ena[0] && ena[1]) |=> (shift_reg == { $past(shift_reg[0]), $past(shift_reg[98:1]) })
    );

    // When load=0 and ena==2'b00, hold value across the clock.
    check_shift_hold_when_idle: assert property (
        @(posedge clk) (!load && (ena == 2'b00)) |=> (shift_reg == $past(shift_reg))
    );

    // Any change to shift_reg occurs only when load or an enable was set in prior cycle.
    check_shift_change_requires_ctrl: assert property (
        @(posedge clk) (shift_reg != $past(shift_reg)) |-> ($past(load || ena[0] || ena[1]))
    );

    ///// Output mux rules /////
    // For ena != 2'b01, upper nibble of out is always zero.
    check_out_upper_zero_when_ena_not01: assert property (
        @(posedge clk) (ena != 2'b01) |-> (out[7:4] == 4'b0000)
    );

    // For sel 110 or 111, output is zero regardless of ena.
    check_out_zero_when_sel_invalid: assert property (
        @(posedge clk) (sel inside {3'b110,3'b111}) |-> (out == 8'b0)
    );

    // When ena == 2'b01, out replicates the selected 4-bit value to both nibbles (halves equal).
    check_out_halves_equal_when_ena01: assert property (
        @(posedge clk) (ena == 2'b01) |-> (out[7:4] == out[3:0])
    );

    // For ena in {00,10,11}, low nibble equals the selected data nibble (sel=000).
    check_out_low_matches_sel0_e001011: assert property (
        @(posedge clk) (sel == 3'd0) && (ena inside {2'b00,2'b10,2'b11}) |-> (out[3:0] == data0)
    );
    // For ena == 01, both nibbles equal selected data nibble (sel=000).
    check_out_rep_sel0_e01: assert property (
        @(posedge clk) (sel == 3'd0) && (ena == 2'b01) |-> ((out[3:0] == data0) && (out[7:4] == data0))
    );

    // For sel=001.
    check_out_low_matches_sel1_e001011: assert property (
        @(posedge clk) (sel == 3'd1) && (ena inside {2'b00,2'b10,2'b11}) |-> (out[3:0] == data1)
    );
    check_out_rep_sel1_e01: assert property (
        @(posedge clk) (sel == 3'd1) && (ena == 2'b01) |-> ((out[3:0] == data1) && (out[7:4] == data1))
    );

    // For sel=010.
    check_out_low_matches_sel2_e001011: assert property (
        @(posedge clk) (sel == 3'd2) && (ena inside {2'b00,2'b10,2'b11}) |-> (out[3:0] == data2)
    );
    check_out_rep_sel2_e01: assert property (
        @(posedge clk) (sel == 3'd2) && (ena == 2'b01) |-> ((out[3:0] == data2) && (out[7:4] == data2))
    );

    // For sel=011.
    check_out_low_matches_sel3_e001011: assert property (
        @(posedge clk) (sel == 3'd3) && (ena inside {2'b00,2'b10,2'b11}) |-> (out[3:0] == data3)
    );
    check_out_rep_sel3_e01: assert property (
        @(posedge clk) (sel == 3'd3) && (ena == 2'b01) |-> ((out[3:0] == data3) && (out[7:4] == data3))
    );

    // For sel=100.
    check_out_low_matches_sel4_e001011: assert property (
        @(posedge clk) (sel == 3'd4) && (ena inside {2'b00,2'b10,2'b11}) |-> (out[3:0] == data4)
    );
    check_out_rep_sel4_e01: assert property (
        @(posedge clk) (sel == 3'd4) && (ena == 2'b01) |-> ((out[3:0] == data4) && (out[7:4] == data4))
    );

    // For sel=101.
    check_out_low_matches_sel5_e001011: assert property (
        @(posedge clk) (sel == 3'd5) && (ena inside {2'b00,2'b10,2'b11}) |-> (out[3:0] == data5)
    );
    check_out_rep_sel5_e01: assert property (
        @(posedge clk) (sel == 3'd5) && (ena == 2'b01) |-> ((out[3:0] == data5) && (out[7:4] == data5))
    );

endmodule