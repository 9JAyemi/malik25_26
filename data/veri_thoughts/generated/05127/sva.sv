module mux2to1_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic sel,
    input logic out
);

    // When sel is low, the output must match a.
    check_sel_low_routes_a: assert property (
        @(posedge clk) (sel === 1'b0) |-> (out === a)
    );

    // When sel is high, the output must match b.
    check_sel_high_routes_b: assert property (
        @(posedge clk) (sel === 1'b1) |-> (out === b)
    );

endmodule