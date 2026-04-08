module mux4to1_sva (
    input logic       clk,
    input logic [1:0] I,
    input logic [1:0] S,
    input logic       O
);

    // When select is 00, output follows I[0].
    check_sel_00_routes_i0: assert property (
        @(posedge clk) (S === 2'b00) |-> (O === I[0])
    );

    // When select is 01, output follows I[1].
    check_sel_01_routes_i1: assert property (
        @(posedge clk) (S === 2'b01) |-> (O === I[1])
    );

    // When select is 10, output is forced low.
    check_sel_10_drives_zero: assert property (
        @(posedge clk) (S === 2'b10) |-> (O === 1'b0)
    );

    // When select is 11, output is forced high.
    check_sel_11_drives_one: assert property (
        @(posedge clk) (S === 2'b11) |-> (O === 1'b1)
    );

endmodule