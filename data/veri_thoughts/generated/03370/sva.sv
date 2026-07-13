module mux_4to1_sva(
    input logic        clk,
    input logic [3:0]  data_in,
    input logic [1:0]  sel,
    input logic        data_out
);

    // When sel is 2'b00, data_out matches data_in[0].
    check_sel_00_routes_data_in0: assert property (
        @(posedge clk) (sel === 2'b00) |-> (data_out === data_in[0])
    );

    // When sel is 2'b01, data_out matches data_in[1].
    check_sel_01_routes_data_in1: assert property (
        @(posedge clk) (sel === 2'b01) |-> (data_out === data_in[1])
    );

    // When sel is 2'b10, data_out matches data_in[2].
    check_sel_10_routes_data_in2: assert property (
        @(posedge clk) (sel === 2'b10) |-> (data_out === data_in[2])
    );

    // When sel is 2'b11, data_out matches data_in[3].
    check_sel_11_routes_data_in3: assert property (
        @(posedge clk) (sel === 2'b11) |-> (data_out === data_in[3])
    );

endmodule