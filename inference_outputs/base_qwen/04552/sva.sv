module logic_function_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);
    // No clock or reset signals are present in the RTL

    // Sequential logic behavior: Y is driven by the outputs of the logic gates
    // at the posedge of the implicit clock (assuming a clock is driving the logic)
    sequential_logic: assert property (
        @(posedge clk) disable iff (!resetn) Y == (A2 | A1) & ~(B2 | B1) & C1
    );
endmodule