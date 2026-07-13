module conditional_output_sva (
    input  logic CLK,  // external sampling clock (RTL has no clock/reset)
    input  logic A,
    input  logic B,
    input  logic C,
    input  logic X
);
    // X must equal ternary expression every cycle.
    check_mux_equation: assert property (
        @(posedge CLK) X == ((A == 1'b1) ? B : C)
    );

    // When A is 1, X must equal B.
    check_select_true_path: assert property (
        @(posedge CLK) (A == 1'b1) |-> (X == B)
    );

    // When A is 0, X must equal C.
    check_select_false_path: assert property (
        @(posedge CLK) (A == 1'b0) |-> (X == C)
    );

    // When B equals C, X must equal that common value.
    check_equal_data_inputs: assert property (
        @(posedge CLK) (B == C) |-> (X == B)
    );
endmodule