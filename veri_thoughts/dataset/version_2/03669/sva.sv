module top_module_sva (
    input logic        clk,
    input logic [1:0]  sel,
    input logic [7:0]  data0,
    input logic [7:0]  data1,
    input logic [7:0]  data2,
    input logic [7:0]  data3,
    input logic [7:0]  out
);

    // When sel is 00, out is the low 8 bits of data0 multiplied by 8'hFF.
    check_sel_00_product: assert property (
        @(posedge clk)
        (sel == 2'b00) |-> ({8'b0, out} == ((data0 * 8'hFF) & 16'h00FF))
    );

    // When sel is 01, out is the low 8 bits of data1 multiplied by 8'hFF.
    check_sel_01_product: assert property (
        @(posedge clk)
        (sel == 2'b01) |-> ({8'b0, out} == ((data1 * 8'hFF) & 16'h00FF))
    );

    // When sel is 10, out is the low 8 bits of data2 multiplied by 8'hFF.
    check_sel_10_product: assert property (
        @(posedge clk)
        (sel == 2'b10) |-> ({8'b0, out} == ((data2 * 8'hFF) & 16'h00FF))
    );

    // When sel is 11, out is the low 8 bits of data3 multiplied by 8'hFF.
    check_sel_11_product: assert property (
        @(posedge clk)
        (sel == 2'b11) |-> ({8'b0, out} == ((data3 * 8'hFF) & 16'h00FF))
    );

    // If all inputs are stable, the combinational output must remain stable.
    check_stable_inputs_keep_output_stable: assert property (
        @(posedge clk)
        $stable(sel) && $stable(data0) && $stable(data1) && $stable(data2) && $stable(data3) |-> $stable(out)
    );

    // With sel held at 00, only data0 can affect out.
    check_sel_00_selected_input_only: assert property (
        @(posedge clk)
        (sel == 2'b00) && $stable(sel) && $stable(data0) |-> $stable(out)
    );

    // With sel held at 01, only data1 can affect out.
    check_sel_01_selected_input_only: assert property (
        @(posedge clk)
        (sel == 2'b01) && $stable(sel) && $stable(data1) |-> $stable(out)
    );

    // With sel held at 10, only data2 can affect out.
    check_sel_10_selected_input_only: assert property (
        @(posedge clk)
        (sel == 2'b10) && $stable(sel) && $stable(data2) |-> $stable(out)
    );

    // With sel held at 11, only data3 can affect out.
    check_sel_11_selected_input_only: assert property (
        @(posedge clk)
        (sel == 2'b11) && $stable(sel) && $stable(data3) |-> $stable(out)
    );

endmodule