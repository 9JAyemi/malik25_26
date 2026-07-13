module mux4to1_sva (
    // DUT ports
    input logic [15:0] data0,
    input logic [15:0] data1,
    input logic [15:0] data2,
    input logic [15:0] data3,
    input logic [1:0]  selectinput,
    input logic [15:0] out,
    // External sampling clock for SVA (DUT has no clock/reset)
    input logic clk
);
    // Notes: DUT is pure combinational 4:1 MUX; no reset present. Assertions are sampled on external clk.

    // When select == 2'b00, out must equal data0.
    check_sel00_out_data0: assert property (
        @(posedge clk) disable iff (1'b0) (selectinput === 2'b00) |-> (out == data0)
    );

    // When select == 2'b01, out must equal data1.
    check_sel01_out_data1: assert property (
        @(posedge clk) disable iff (1'b0) (selectinput === 2'b01) |-> (out == data1)
    );

    // When select == 2'b10, out must equal data2.
    check_sel10_out_data2: assert property (
        @(posedge clk) disable iff (1'b0) (selectinput === 2'b10) |-> (out == data2)
    );

    // When select == 2'b11, out must equal data3.
    check_sel11_out_data3: assert property (
        @(posedge clk) disable iff (1'b0) (selectinput === 2'b11) |-> (out == data3)
    );

    // With select[1]==0, out equals 2:1 mux of data0/data1 selected by select[0].
    check_lower_branch_mux: assert property (
        @(posedge clk) disable iff (1'b0) (selectinput[1] === 1'b0) |-> (out == ((selectinput[0] == 1'b0) ? data0 : data1))
    );

    // With select[1]==1, out equals 2:1 mux of data2/data3 selected by select[0].
    check_upper_branch_mux: assert property (
        @(posedge clk) disable iff (1'b0) (selectinput[1] === 1'b1) |-> (out == ((selectinput[0] == 1'b0) ? data2 : data3))
    );

    // Out equals the exact nested conditional structure implemented in RTL.
    check_full_mux_equation: assert property (
        @(posedge clk) disable iff (1'b0)
            out == ((selectinput[1] == 1'b0)
                      ? ((selectinput[0] == 1'b0) ? data0 : data1)
                      : ((selectinput[0] == 1'b0) ? data2 : data3))
    );

endmodule