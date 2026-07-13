module mux_2to1_sva (
    input logic clk,
    input logic [1:0] data_in,
    input logic sel,
    input logic data_out
);

    // When sel is 0, the output matches data_in[0].
    check_select_low: assert property (
        @(posedge clk) (sel === 1'b0) |-> (data_out === data_in[0])
    );

    // When sel is 1, the output matches data_in[1].
    check_select_high: assert property (
        @(posedge clk) (sel === 1'b1) |-> (data_out === data_in[1])
    );

    // The output always matches the RTL mux equation.
    check_mux_equation: assert property (
        @(posedge clk) data_out === ((sel == 1'b0) ? data_in[0] : data_in[1])
    );

endmodule