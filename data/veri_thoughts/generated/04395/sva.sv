module logic_gate_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic [1:0] OP,
    input logic Y
);

    // OP=00 selects the AND result.
    check_and_select: assert property (
        @(posedge clk) (OP == 2'b00) |-> (Y == (A & B))
    );

    // OP=01 selects the OR result.
    check_or_select: assert property (
        @(posedge clk) (OP == 2'b01) |-> (Y == (A | B))
    );

    // OP=10 selects the XOR result.
    check_xor_select: assert property (
        @(posedge clk) (OP == 2'b10) |-> (Y == (A ^ B))
    );

    // OP=11 selects the inversion of A.
    check_not_select: assert property (
        @(posedge clk) (OP == 2'b11) |-> (Y == (~A))
    );

    // Y always matches the function selected by OP.
    check_selected_function: assert property (
        @(posedge clk)
        Y == ((OP == 2'b00) ? (A & B) :
              (OP == 2'b01) ? (A | B) :
              (OP == 2'b10) ? (A ^ B) :
                              (~A))
    );

endmodule