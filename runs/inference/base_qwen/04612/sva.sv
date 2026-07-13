module logic_module_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic E,
    input logic F,
    input logic G,
    input logic H,
    output logic X
);
    // Combinational logic, but still use @(posedge clk) for assertions

    // X is the result of a combination of AND and OR operations
    // Ensure that X is correctly computed based on the inputs
    check_X_computation: assert property (
        @(posedge clk) disable iff (!reset_n) (X == (A && B || C && D || !(E && F) || !(G && H)))
    );
endmodule