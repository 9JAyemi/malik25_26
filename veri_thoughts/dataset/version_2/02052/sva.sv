module top_module_sva (
    input logic CLK,
    input logic a,
    input logic b,
    input logic c,
    input logic [2:0] sel,
    input logic [3:0] data0,
    input logic [3:0] data1,
    input logic [3:0] data2,
    input logic [3:0] data3,
    input logic [3:0] data4,
    input logic [3:0] data5,
    input logic [7:0] final_output
);
    ///// wire_mux mapping to final_output[3:0] /////
    // final_output[3] must mirror a.
    check_w_maps_a: assert property (
        @(posedge CLK) disable iff (1'b0) final_output[3] == a
    );
    // final_output[2] must reflect b (b ? 1 : 0).
    check_x_maps_b: assert property (
        @(posedge CLK) disable iff (1'b0) final_output[2] == b
    );
    // final_output[1] must reflect b (b ? 1 : 0).
    check_y_maps_b: assert property (
        @(posedge CLK) disable iff (1'b0) final_output[1] == b
    );
    // final_output[0] must mirror c.
    check_z_maps_c: assert property (
        @(posedge CLK) disable iff (1'b0) final_output[0] == c
    );
    // final_output[2] and final_output[1] must always be identical.
    check_x_equals_y: assert property (
        @(posedge CLK) disable iff (1'b0) final_output[2] == final_output[1]
    );

    ///// mux_sel routing to final_output[7:4] /////
    // When sel==000, out must equal data0.
    check_sel_000_data0: assert property (
        @(posedge CLK) disable iff (1'b0) (sel != 3'b000) || (final_output[7:4] == data0)
    );
    // When sel==001, out must equal data1.
    check_sel_001_data1: assert property (
        @(posedge CLK) disable iff (1'b0) (sel != 3'b001) || (final_output[7:4] == data1)
    );
    // When sel==010, out must equal data2.
    check_sel_010_data2: assert property (
        @(posedge CLK) disable iff (1'b0) (sel != 3'b010) || (final_output[7:4] == data2)
    );
    // When sel==011, out must equal data3.
    check_sel_011_data3: assert property (
        @(posedge CLK) disable iff (1'b0) (sel != 3'b011) || (final_output[7:4] == data3)
    );
    // When sel==100, out must equal data4.
    check_sel_100_data4: assert property (
        @(posedge CLK) disable iff (1'b0) (sel != 3'b100) || (final_output[7:4] == data4)
    );
    // When sel==101, out must equal data5.
    check_sel_101_data5: assert property (
        @(posedge CLK) disable iff (1'b0) (sel != 3'b101) || (final_output[7:4] == data5)
    );
    // When sel==110, out must be zero (default case).
    check_sel_110_zero: assert property (
        @(posedge CLK) disable iff (1'b0) (sel != 3'b110) || (final_output[7:4] == 4'b0000)
    );
    // When sel==111, out must be zero (default case).
    check_sel_111_zero: assert property (
        @(posedge CLK) disable iff (1'b0) (sel != 3'b111) || (final_output[7:4] == 4'b0000)
    );
endmodule