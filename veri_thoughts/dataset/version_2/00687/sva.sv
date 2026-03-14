module top_module_sva (
    input logic a,
    input logic b,
    input logic sel_b1,
    input logic sel_b2,
    input logic clk,
    input logic [2:0] sel, 
    input logic [3:0] data0,
    input logic [3:0] data1,
    input logic [3:0] data2,
    input logic [3:0] data3,
    input logic [3:0] data4,
    input logic [3:0] data5,
    input logic [7:0] sum_out,
    input logic out_2to1_mux,
    input logic [3:0] out_6to1_mux
);

    ///// 2:1 registered select /////
    // When both selects are HIGH, next out_2to1_mux captures b.
    two_to_one_routes_b: assert property (
        @(posedge clk) (sel_b1 && sel_b2) |=> (out_2to1_mux == $past(b))
    );
    // When either select is LOW, next out_2to1_mux captures a.
    two_to_one_routes_a: assert property (
        @(posedge clk) !(sel_b1 && sel_b2) |=> (out_2to1_mux == $past(a))
    );

    ///// 6:1 combinational mux /////
    // sel==000 selects data0.
    mux6_sel_000: assert property (
        @(posedge clk) (sel == 3'b000) |-> (out_6to1_mux == data0)
    );
    // sel==001 selects data1.
    mux6_sel_001: assert property (
        @(posedge clk) (sel == 3'b001) |-> (out_6to1_mux == data1)
    );
    // sel==010 selects data2.
    mux6_sel_010: assert property (
        @(posedge clk) (sel == 3'b010) |-> (out_6to1_mux == data2)
    );
    // sel==011 selects data3.
    mux6_sel_011: assert property (
        @(posedge clk) (sel == 3'b011) |-> (out_6to1_mux == data3)
    );
    // sel==100 selects data4.
    mux6_sel_100: assert property (
        @(posedge clk) (sel == 3'b100) |-> (out_6to1_mux == data4)
    );
    // sel==101 selects data5.
    mux6_sel_101: assert property (
        @(posedge clk) (sel == 3'b101) |-> (out_6to1_mux == data5)
    );
    // sel==110 defaults to data0.
    mux6_default_110: assert property (
        @(posedge clk) (sel == 3'b110) |-> (out_6to1_mux == data0)
    );
    // sel==111 defaults to data0.
    mux6_default_111: assert property (
        @(posedge clk) (sel == 3'b111) |-> (out_6to1_mux == data0)
    );

    ///// Sum register /////
    // Next sum_out[3:0] equals prior out_2to1_mux + out_6to1_mux (4-bit result).
    sum_lowbits_match: assert property (
        @(posedge clk) 1'b1 |=> (sum_out[3:0] == ($past(out_2to1_mux) + $past(out_6to1_mux)))
    );
    // Next sum_out[7:4] are always zero due to 4-bit addition zero-extension.
    sum_upper_zero: assert property (
        @(posedge clk) 1'b1 |=> (sum_out[7:4] == 4'b0000)
    );

endmodule