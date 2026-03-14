module top_module_sva (
    input logic clk,
    input logic [15:0] in,
    input logic [2:0] sel,
    input logic [3:0] data0,
    input logic [3:0] data1,
    input logic [3:0] data2,
    input logic [3:0] data3,
    input logic [3:0] data4,
    input logic [3:0] data5,
    input logic [7:0] out_hi,
    input logic [7:0] out_lo
);
    // out_lo equals bitwise AND of upper and lower bytes of in.
    check_out_lo_is_and_of_in_halves: assert property (
        @(posedge clk) out_lo == (in[15:8] & in[7:0])
    );

    // out_hi equals zero-extended selected data input per sel.
    check_out_hi_mux_full_zero_extended: assert property (
        @(posedge clk)
            out_hi == {4'b0000,
                       (sel == 3'd0) ? data0 :
                       (sel == 3'd1) ? data1 :
                       (sel == 3'd2) ? data2 :
                       (sel == 3'd3) ? data3 :
                       (sel == 3'd4) ? data4 : data5}
    );

    // When sel==0, out_hi lower nibble equals data0, upper nibble zero.
    check_out_hi_sel0_zero_extended: assert property (
        @(posedge clk) (sel == 3'd0) |-> (out_hi[3:0] == data0) && (out_hi[7:4] == 4'b0000)
    );

    // When sel==1, out_hi lower nibble equals data1, upper nibble zero.
    check_out_hi_sel1_zero_extended: assert property (
        @(posedge clk) (sel == 3'd1) |-> (out_hi[3:0] == data1) && (out_hi[7:4] == 4'b0000)
    );

    // When sel==2, out_hi lower nibble equals data2, upper nibble zero.
    check_out_hi_sel2_zero_extended: assert property (
        @(posedge clk) (sel == 3'd2) |-> (out_hi[3:0] == data2) && (out_hi[7:4] == 4'b0000)
    );

    // When sel==3, out_hi lower nibble equals data3, upper nibble zero.
    check_out_hi_sel3_zero_extended: assert property (
        @(posedge clk) (sel == 3'd3) |-> (out_hi[3:0] == data3) && (out_hi[7:4] == 4'b0000)
    );

    // When sel==4, out_hi lower nibble equals data4, upper nibble zero.
    check_out_hi_sel4_zero_extended: assert property (
        @(posedge clk) (sel == 3'd4) |-> (out_hi[3:0] == data4) && (out_hi[7:4] == 4'b0000)
    );

    // When sel is 5..7, out_hi lower nibble equals data5, upper nibble zero.
    check_out_hi_sel_default_zero_extended: assert property (
        @(posedge clk) (sel inside {[3'd5:3'd7]}) |-> (out_hi[3:0] == data5) && (out_hi[7:4] == 4'b0000)
    );

    // Changes on in alone do not affect out_hi.
    check_out_hi_independent_of_in: assert property (
        @(posedge clk)
            ($changed(in) && $stable(sel) && $stable(data0) && $stable(data1) && $stable(data2) &&
             $stable(data3) && $stable(data4) && $stable(data5)) |-> $stable(out_hi)
    );

    // Changes on sel/data alone do not affect out_lo.
    check_out_lo_independent_of_sel_data: assert property (
        @(posedge clk)
            ($stable(in) && $changed({sel, data0, data1, data2, data3, data4, data5})) |-> $stable(out_lo)
    );
endmodule