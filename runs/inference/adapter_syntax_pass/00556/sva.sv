module my_module_sva (
    input logic clk,
    input logic Z,
    input logic A,
    input logic TE_B
);

    // Z must always match the RTL mux equation.
    check_mux_equation: assert property (
        @(posedge clk) Z === (TE_B ? 1'b1 : A)
    );

    // When TE_B is high, Z must be forced high.
    check_select_high_forces_one: assert property (
        @(posedge clk) TE_B |-> (Z === 1'b1)
    );

    // When TE_B is low, Z must follow A.
    check_select_low_follows_a: assert property (
        @(posedge clk) !TE_B |-> (Z === A)
    );

endmodule