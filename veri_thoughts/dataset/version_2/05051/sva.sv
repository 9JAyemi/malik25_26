module mux_4to1_sva (
    input logic clk,
    input logic [3:0] inputs,
    input logic [1:0] select,
    input logic out
);

    // When select is 00, out matches inputs[0].
    check_select_00_routes_input0: assert property (
        @(posedge clk) disable iff (1'b0)
        (select == 2'b00) |-> (out == inputs[0])
    );

    // When select is 01, out matches inputs[1].
    check_select_01_routes_input1: assert property (
        @(posedge clk) disable iff (1'b0)
        (select == 2'b01) |-> (out == inputs[1])
    );

    // When select is 10, out matches inputs[2].
    check_select_10_routes_input2: assert property (
        @(posedge clk) disable iff (1'b0)
        (select == 2'b10) |-> (out == inputs[2])
    );

    // When select is 11, out matches inputs[3].
    check_select_11_routes_input3: assert property (
        @(posedge clk) disable iff (1'b0)
        (select == 2'b11) |-> (out == inputs[3])
    );

    // If select stays at 00 and inputs[0] is stable, out stays stable.
    check_select_00_stable_selected_input_keeps_out_stable: assert property (
        @(posedge clk) disable iff (1'b0)
        (select == 2'b00 && $stable(select) && $stable(inputs[0])) |-> $stable(out)
    );

    // If select stays at 01 and inputs[1] is stable, out stays stable.
    check_select_01_stable_selected_input_keeps_out_stable: assert property (
        @(posedge clk) disable iff (1'b0)
        (select == 2'b01 && $stable(select) && $stable(inputs[1])) |-> $stable(out)
    );

    // If select stays at 10 and inputs[2] is stable, out stays stable.
    check_select_10_stable_selected_input_keeps_out_stable: assert property (
        @(posedge clk) disable iff (1'b0)
        (select == 2'b10 && $stable(select) && $stable(inputs[2])) |-> $stable(out)
    );

    // If select stays at 11 and inputs[3] is stable, out stays stable.
    check_select_11_stable_selected_input_keeps_out_stable: assert property (
        @(posedge clk) disable iff (1'b0)
        (select == 2'b11 && $stable(select) && $stable(inputs[3])) |-> $stable(out)
    );

endmodule