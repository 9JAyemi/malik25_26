module my_2to1_mux_sva (
    input logic        clk,
    input logic [16:0] MO,
    input logic [16:0] A,
    input logic [16:0] B,
    input logic        S
);

    // MO must always match the mux select expression.
    check_mux_function: assert property (
        @(posedge clk) MO === ((S == 1'b1) ? B : A)
    );

    // When S is low, MO must select A.
    check_select_low_routes_a: assert property (
        @(posedge clk) (S === 1'b0) |-> (MO === A)
    );

    // When S is high, MO must select B.
    check_select_high_routes_b: assert property (
        @(posedge clk) (S === 1'b1) |-> (MO === B)
    );

    // If both inputs are equal, MO must equal that common value.
    check_equal_inputs_passthrough: assert property (
        @(posedge clk) (A === B) |-> (MO === A)
    );

    // With stable select and selected input, MO must remain stable.
    check_stable_when_select_and_input_stable: assert property (
        @(posedge clk) ($stable(S) && ((S === 1'b0) ? $stable(A) : $stable(B))) |-> $stable(MO)
    );

    // With stable select and both inputs stable, MO must remain stable.
    check_stable_when_select_and_inputs_stable: assert property (
        @(posedge clk) ($stable(S) && $stable(A) && $stable(B)) |-> $stable(MO)
    );

endmodule