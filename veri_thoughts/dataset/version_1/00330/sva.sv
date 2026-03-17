module full_adder_sva(
    input logic clk,
    input logic A,
    input logic B,
    input logic Cin,
    input logic Cout,
    input logic Sum
);

    // Sum matches three-input parity.
    check_sum_function: assert property (
        @(posedge clk) Sum === (A ^ B ^ Cin)
    );

    // Carry matches the three-input majority function.
    check_carry_function: assert property (
        @(posedge clk) Cout === ((A & B) | (B & Cin) | (Cin & A))
    );

    // All-zero inputs produce zero outputs.
    check_zero_input_case: assert property (
        @(posedge clk)
        ((A === 1'b0) && (B === 1'b0) && (Cin === 1'b0))
        |-> ((Sum === 1'b0) && (Cout === 1'b0))
    );

    // Exactly one high input produces sum high and carry low.
    check_single_high_input_case: assert property (
        @(posedge clk)
        (((A === 1'b1) && (B === 1'b0) && (Cin === 1'b0)) ||
         ((A === 1'b0) && (B === 1'b1) && (Cin === 1'b0)) ||
         ((A === 1'b0) && (B === 1'b0) && (Cin === 1'b1)))
        |-> ((Sum === 1'b1) && (Cout === 1'b0))
    );

    // Exactly two high inputs produce sum low and carry high.
    check_two_high_input_case: assert property (
        @(posedge clk)
        (((A === 1'b1) && (B === 1'b1) && (Cin === 1'b0)) ||
         ((A === 1'b1) && (B === 1'b0) && (Cin === 1'b1)) ||
         ((A === 1'b0) && (B === 1'b1) && (Cin === 1'b1)))
        |-> ((Sum === 1'b0) && (Cout === 1'b1))
    );

    // All-high inputs produce sum high and carry high.
    check_all_high_input_case: assert property (
        @(posedge clk)
        ((A === 1'b1) && (B === 1'b1) && (Cin === 1'b1))
        |-> ((Sum === 1'b1) && (Cout === 1'b1))
    );

endmodule

module mux2_sva(
    input logic clk,
    input logic I0,
    input logic I1,
    input logic S,
    input logic O
);

    // Output matches the mux select expression.
    check_mux_function: assert property (
        @(posedge clk) O === (S ? I1 : I0)
    );

    // Low select chooses I0.
    check_select_low_path: assert property (
        @(posedge clk) (S === 1'b0) |-> (O === I0)
    );

    // High select chooses I1.
    check_select_high_path: assert property (
        @(posedge clk) (S === 1'b1) |-> (O === I1)
    );

    // Equal data inputs pass through regardless of select.
    check_equal_inputs_passthrough: assert property (
        @(posedge clk) (I0 === I1) |-> (O === I0)
    );

endmodule