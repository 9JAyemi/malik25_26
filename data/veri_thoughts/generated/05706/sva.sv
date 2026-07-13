module cycloneive_b5mux21_extended_sva (
    input logic        clk,
    input logic [31:0] MO,
    input logic [31:0] A,
    input logic [31:0] B,
    input logic        S
);

    // MO always matches the implemented mux equation.
    check_mux_equation: assert property (
        @(posedge clk) MO === ((S == 1'b1) ? B : A)
    );

    // When S is low, MO follows A.
    check_select_low_routes_a: assert property (
        @(posedge clk) (S === 1'b0) |-> (MO === A)
    );

    // When S is high, MO follows B.
    check_select_high_routes_b: assert property (
        @(posedge clk) (S === 1'b1) |-> (MO === B)
    );

    // If both inputs are identical, MO matches that common value.
    check_equal_inputs_preserved: assert property (
        @(posedge clk) (A === B) |-> (MO === A)
    );

endmodule