module mux4x1_sva (
    input logic        clk,
    input logic [7:0]  A,
    input logic [7:0]  B,
    input logic [7:0]  C,
    input logic [7:0]  D,
    input logic [1:0]  S,
    input logic [7:0]  Y
);

    // S=00 routes A to Y.
    check_select_a: assert property (
        @(posedge clk) (S === 2'b00) |-> (Y === A)
    );

    // S=01 routes B to Y.
    check_select_b: assert property (
        @(posedge clk) (S === 2'b01) |-> (Y === B)
    );

    // S=10 routes C to Y.
    check_select_c: assert property (
        @(posedge clk) (S === 2'b10) |-> (Y === C)
    );

    // S=11 routes D to Y.
    check_select_d: assert property (
        @(posedge clk) (S === 2'b11) |-> (Y === D)
    );

endmodule