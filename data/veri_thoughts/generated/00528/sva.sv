module mux2x4_assertions (
    input logic clk,
    input logic [1:0] data0,
    input logic [1:0] data1,
    input logic [1:0] data2,
    input logic [1:0] data3,
    input logic [1:0] selectInput,
    input logic [1:0] out
);

    // When selectInput is 00, out must equal data0.
    check_select_00: assert property (
        @(posedge clk) (selectInput === 2'b00) |-> (out === data0)
    );

    // When selectInput is 01, out must equal data1.
    check_select_01: assert property (
        @(posedge clk) (selectInput === 2'b01) |-> (out === data1)
    );

    // When selectInput is 10, out must equal data2.
    check_select_10: assert property (
        @(posedge clk) (selectInput === 2'b10) |-> (out === data2)
    );

    // When selectInput is 11, out must equal data3.
    check_select_11: assert property (
        @(posedge clk) (selectInput === 2'b11) |-> (out === data3)
    );

    // When selectInput contains X or Z, out must take the default value 00.
    check_default_on_unknown_select: assert property (
        @(posedge clk) $isunknown(selectInput) |-> (out === 2'b00)
    );

endmodule