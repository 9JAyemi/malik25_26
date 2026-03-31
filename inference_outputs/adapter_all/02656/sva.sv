module wireless_communication_block_sva (
    input logic        clk,
    input logic [7:0]  data_in,
    input logic [1:0]  ctrl,
    input logic [7:0]  data_out
);

    // ctrl=00 routes data_in directly to data_out.
    check_ctrl_00_routes_data: assert property (
        @(posedge clk) (ctrl == 2'b00) |-> (data_out == data_in)
    );

    // ctrl=01 routes data_in directly to data_out.
    check_ctrl_01_routes_data: assert property (
        @(posedge clk) (ctrl == 2'b01) |-> (data_out == data_in)
    );

    // ctrl=10 routes data_in directly to data_out.
    check_ctrl_10_routes_data: assert property (
        @(posedge clk) (ctrl == 2'b10) |-> (data_out == data_in)
    );

    // ctrl=11 routes data_in directly to data_out.
    check_ctrl_11_routes_data: assert property (
        @(posedge clk) (ctrl == 2'b11) |-> (data_out == data_in)
    );

    // With ctrl=00 held and data_in stable, data_out remains stable.
    check_ctrl_00_stable_input_keeps_output_stable: assert property (
        @(posedge clk) (ctrl == 2'b00 && $stable(ctrl) && $stable(data_in)) |-> $stable(data_out)
    );

    // With ctrl=01 held and data_in stable, data_out remains stable.
    check_ctrl_01_stable_input_keeps_output_stable: assert property (
        @(posedge clk) (ctrl == 2'b01 && $stable(ctrl) && $stable(data_in)) |-> $stable(data_out)
    );

    // With ctrl=10 held and data_in stable, data_out remains stable.
    check_ctrl_10_stable_input_keeps_output_stable: assert property (
        @(posedge clk) (ctrl == 2'b10 && $stable(ctrl) && $stable(data_in)) |-> $stable(data_out)
    );

    // With ctrl=11 held and data_in stable, data_out remains stable.
    check_ctrl_11_stable_input_keeps_output_stable: assert property (
        @(posedge clk) (ctrl == 2'b11 && $stable(ctrl) && $stable(data_in)) |-> $stable(data_out)
    );

endmodule