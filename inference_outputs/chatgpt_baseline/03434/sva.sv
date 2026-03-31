module top_module_assertions (
    input logic        clk,
    input logic [2:0]  sel,
    input logic [3:0]  data0,
    input logic [3:0]  data1,
    input logic [3:0]  data2,
    input logic [3:0]  data3,
    input logic [3:0]  data4,
    input logic [3:0]  data5,
    input logic [3:0]  out_mux,
    input logic [2:0]  out_3bit,
    input logic        o2,
    input logic        o1,
    input logic        o0,
    input logic [6:0]  final_out
);

    // out_mux selects data0 when sel is 0.
    check_out_mux_sel0: assert property (
        @(posedge clk) (sel == 3'd0) |-> (out_mux == data0)
    );

    // out_mux selects data1 when sel is 1.
    check_out_mux_sel1: assert property (
        @(posedge clk) (sel == 3'd1) |-> (out_mux == data1)
    );

    // out_mux selects data2 when sel is 2.
    check_out_mux_sel2: assert property (
        @(posedge clk) (sel == 3'd2) |-> (out_mux == data2)
    );

    // out_mux selects data3 when sel is 3.
    check_out_mux_sel3: assert property (
        @(posedge clk) (sel == 3'd3) |-> (out_mux == data3)
    );

    // out_mux selects data4 when sel is 4.
    check_out_mux_sel4: assert property (
        @(posedge clk) (sel == 3'd4) |-> (out_mux == data4)
    );

    // out_mux selects data5 when sel is 5.
    check_out_mux_sel5: assert property (
        @(posedge clk) (sel == 3'd5) |-> (out_mux == data5)
    );

    // out_mux is zero when sel is outside 0 through 5.
    check_out_mux_default_zero: assert property (
        @(posedge clk) ((sel == 3'd6) || (sel == 3'd7)) |-> (out_mux == 4'b0000)
    );

    // out_3bit mirrors sel.
    check_out_3bit_matches_sel: assert property (
        @(posedge clk) out_3bit == sel
    );

    // o2 mirrors sel[2].
    check_o2_matches_sel_bit2: assert property (
        @(posedge clk) o2 == sel[2]
    );

    // o1 mirrors sel[1].
    check_o1_matches_sel_bit1: assert property (
        @(posedge clk) o1 == sel[1]
    );

    // o0 mirrors sel[0].
    check_o0_matches_sel_bit0: assert property (
        @(posedge clk) o0 == sel[0]
    );

    // final_out is the zero-extended sum of the selected mux input and sel.
    check_final_out_sum: assert property (
        @(posedge clk)
        final_out ==
        ({3'b000, ((sel == 3'd0) ? data0 :
                   (sel == 3'd1) ? data1 :
                   (sel == 3'd2) ? data2 :
                   (sel == 3'd3) ? data3 :
                   (sel == 3'd4) ? data4 :
                   (sel == 3'd5) ? data5 : 4'b0000)} + {4'b0000, sel})
    );

endmodule