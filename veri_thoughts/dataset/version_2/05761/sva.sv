module my_2to1_mux_assertions (
    input logic        clk,
    input logic [16:0] MO,
    input logic [16:0] A,
    input logic [16:0] B,
    input logic        S
);

    // MO must match the mux expression implemented in the RTL.
    check_mux_equation: assert property (
        @(posedge clk) MO === ((S == 1'b1) ? B : A)
    );

    // A high select routes B to the output.
    check_select_high_routes_b: assert property (
        @(posedge clk) (S === 1'b1) |-> (MO === B)
    );

    // A low select routes A to the output.
    check_select_low_routes_a: assert property (
        @(posedge clk) (S === 1'b0) |-> (MO === A)
    );

    // Equal inputs make the output independent of select.
    check_equal_inputs_pass_through: assert property (
        @(posedge clk) (A === B) |-> (MO === A)
    );

endmodule