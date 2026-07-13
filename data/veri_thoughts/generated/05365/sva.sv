module mux4_enable_sva (
    input logic clk,
    input logic [3:0] data_in,
    input logic [1:0] select,
    input logic enable,
    input logic out
);

    // When disabled, the output is forced low.
    check_disable_forces_low: assert property (
        @(posedge clk) !enable |-> (out == 1'b0)
    );

    // When enabled and select is 00, output matches data_in[0].
    check_select_00_routes_bit0: assert property (
        @(posedge clk) (enable && (select == 2'b00)) |-> (out == data_in[0])
    );

    // When enabled and select is 01, output matches data_in[1].
    check_select_01_routes_bit1: assert property (
        @(posedge clk) (enable && (select == 2'b01)) |-> (out == data_in[1])
    );

    // When enabled and select is 10, output matches data_in[2].
    check_select_10_routes_bit2: assert property (
        @(posedge clk) (enable && (select == 2'b10)) |-> (out == data_in[2])
    );

    // When enabled and select is 11, output matches data_in[3].
    check_select_11_routes_bit3: assert property (
        @(posedge clk) (enable && (select == 2'b11)) |-> (out == data_in[3])
    );

endmodule