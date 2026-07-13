module mux_2to1_enable_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic EN,
    input logic Y
);

    // Y must always match the RTL mux equation.
    check_mux_function: assert property (
        @(posedge clk) Y === (EN ? A : B)
    );

    // When EN is high, Y must select A.
    check_select_a_when_enabled: assert property (
        @(posedge clk) EN |-> (Y === A)
    );

    // When EN is low, Y must select B.
    check_select_b_when_disabled: assert property (
        @(posedge clk) !EN |-> (Y === B)
    );

endmodule