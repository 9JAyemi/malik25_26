module top_module_sva (
    input logic clk,
    input logic [2:0] sel,
    input logic [3:0] data0,
    input logic [3:0] data1,
    input logic [3:0] data2,
    input logic [3:0] data3,
    input logic [3:0] data4,
    input logic [3:0] data5,
    input logic [3:0] out_mux,
    input logic [2:0] out_3bit,
    input logic o2,
    input logic o1,
    input logic o0,
    input logic [6:0] final_out
);

// out_mux selects data0 when sel==0.
    check_mux_sel_0: assert property (
        @(posedge clk) (sel == 3'd0) |-> (out_mux == data0)
    );

// out_mux selects data1 when sel==1.
    check_mux_sel_1: assert property (
        @(posedge clk) (sel == 3'd1) |-> (out_mux == data1)
    );

// out_mux selects data2 when sel==2.
    check_mux_sel_2: assert property (
        @(posedge clk) (sel == 3'd2) |-> (out_mux == data2)
    );

// out_mux selects data3 when sel==3.
    check_mux_sel_3: assert property (
        @(posedge clk) (sel == 3'd3) |-> (out_mux == data3)
    );

// out_mux selects data4 when sel==4.
    check_mux_sel_4: assert property (
        @(posedge clk) (sel == 3'd4) |-> (out_mux == data4)
    );

// out_mux selects data5 when sel==5.
    check_mux_sel_5: assert property (
        @(posedge clk) (sel == 3'd5) |-> (out_mux == data5)
    );

// out_mux is zero when sel is 6 or 7.
    check_mux_default_zero: assert property (
        @(posedge clk) (sel >= 3'd6) |-> (out_mux == 4'b0000)
    );

// out_3bit mirrors sel.
    check_out_3bit_passthrough: assert property (
        @(posedge clk) out_3bit == sel
    );

// o2 is the MSB of sel.
    check_o2_passthrough: assert property (
        @(posedge clk) o2 == sel[2]
    );

// o1 is the middle bit of sel.
    check_o1_passthrough: assert property (
        @(posedge clk) o1 == sel[1]
    );

// o0 is the LSB of sel.
    check_o0_passthrough: assert property (
        @(posedge clk) o0 == sel[0]
    );

// final_out upper bit is the carry from mux_out + sel.
    check_final_out_carry: assert property (
        @(posedge clk) final_out[6] == (({1'b0, out_mux} + {1'b0, sel}) >= 5'd32)
    );

// final_out lower bits are the sum of mux_out and sel.
    check_final_out_sum: assert property (
        @(posedge clk) final_out[5:0] == (({1'b0, out_mux} + {1'b0, sel}) & 6'h3f)
    );

endmodule
