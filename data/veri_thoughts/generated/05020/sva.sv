module mux4to1_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] c,
    input logic [7:0] d,
    input logic [1:0] s,
    input logic [7:0] w
);

    // When select is 00, output must match input a.
    check_select_a: assert property (
        @(posedge clk) (s === 2'b00) |-> (w === a)
    );

    // When select is 01, output must match input b.
    check_select_b: assert property (
        @(posedge clk) (s === 2'b01) |-> (w === b)
    );

    // When select is 10, output must match input c.
    check_select_c: assert property (
        @(posedge clk) (s === 2'b10) |-> (w === c)
    );

    // When select is 11, output must match input d.
    check_select_d: assert property (
        @(posedge clk) (s === 2'b11) |-> (w === d)
    );

endmodule