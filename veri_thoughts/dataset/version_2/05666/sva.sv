module chan_mux_sva (
    input logic        clk,
    input logic [21:0] data0x,
    input logic [21:0] data1x,
    input logic [21:0] data2x,
    input logic [1:0]  sel,
    input logic [21:0] result
);

    // sel=00 routes data0x to result.
    check_sel_00_routes_data0: assert property (
        @(posedge clk) (sel === 2'b00) |-> (result === data0x)
    );

    // sel=01 routes data1x to result.
    check_sel_01_routes_data1: assert property (
        @(posedge clk) (sel === 2'b01) |-> (result === data1x)
    );

    // sel=10 routes data2x to result.
    check_sel_10_routes_data2: assert property (
        @(posedge clk) (sel === 2'b10) |-> (result === data2x)
    );

    // With sel=00, changes on unselected inputs do not change result.
    check_sel_00_ignores_unselected_inputs: assert property (
        @(posedge clk)
        ((sel === 2'b00) && $stable(sel) && $stable(data0x) && ($changed(data1x) || $changed(data2x)))
        |-> $stable(result)
    );

    // With sel=01, changes on unselected inputs do not change result.
    check_sel_01_ignores_unselected_inputs: assert property (
        @(posedge clk)
        ((sel === 2'b01) && $stable(sel) && $stable(data1x) && ($changed(data0x) || $changed(data2x)))
        |-> $stable(result)
    );

    // With sel=10, changes on unselected inputs do not change result.
    check_sel_10_ignores_unselected_inputs: assert property (
        @(posedge clk)
        ((sel === 2'b10) && $stable(sel) && $stable(data2x) && ($changed(data0x) || $changed(data1x)))
        |-> $stable(result)
    );

    // If sel and all inputs are stable, result remains stable.
    check_result_stable_when_inputs_and_sel_stable: assert property (
        @(posedge clk)
        ($stable(sel) && $stable(data0x) && $stable(data1x) && $stable(data2x))
        |-> $stable(result)
    );

endmodule