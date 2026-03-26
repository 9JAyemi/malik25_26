module sky130_fd_sc_hvl__nor2_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B
);

    // Y must implement the 2-input NOR equation.
    check_nor_equation: assert property (
        @(posedge clk) Y == ~(A | B)
    );

    // Both inputs low must drive Y high.
    check_nor_00: assert property (
        @(posedge clk) (!A && !B) |-> Y
    );

    // A low and B high must drive Y low.
    check_nor_01: assert property (
        @(posedge clk) (!A && B) |-> !Y
    );

    // A high and B low must drive Y low.
    check_nor_10: assert property (
        @(posedge clk) (A && !B) |-> !Y
    );

    // Both inputs high must drive Y low.
    check_nor_11: assert property (
        @(posedge clk) (A && B) |-> !Y
    );

endmodule