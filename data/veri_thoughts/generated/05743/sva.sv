module sel_logic_sva (
    input logic clk,
    input logic [1:0] sel,
    input logic A,
    input logic B,
    input logic Y
);

    // RTL is combinational with no reset; clk is the SVA sampling clock.

    // Y must match the selected boolean function.
    check_y_functional_equivalence: assert property (
        @(posedge clk)
        Y == ((sel == 2'b00) ? (A ^ B) :
              (sel == 2'b01) ? (A & B) :
              (sel == 2'b10) ? (A | B) :
                               ~(A & B))
    );

    // sel=00 selects XOR of A and B.
    check_sel_xor: assert property (
        @(posedge clk)
        (sel == 2'b00) |-> (Y == (A ^ B))
    );

    // sel=01 selects AND of A and B.
    check_sel_and: assert property (
        @(posedge clk)
        (sel == 2'b01) |-> (Y == (A & B))
    );

    // sel=10 selects OR of A and B.
    check_sel_or: assert property (
        @(posedge clk)
        (sel == 2'b10) |-> (Y == (A | B))
    );

    // sel=11 selects NAND of A and B.
    check_sel_nand: assert property (
        @(posedge clk)
        (sel == 2'b11) |-> (Y == ~(A & B))
    );

endmodule