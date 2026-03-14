module mux2to1_sva (
    input  logic CLK, // sampling clock for assertions (DUT is combinational)
    input  logic A,
    input  logic B,
    input  logic S,
    input  logic Z
);
    // Z equals selected input per S.
    check_mux_function: assert property (
        @(posedge CLK) disable iff (1'b0) Z == (S ? B : A)
    );

    // When S is 0, Z equals A.
    check_select0_path: assert property (
        @(posedge CLK) disable iff (1'b0) (S == 1'b0) |-> (Z == A)
    );

    // When S is 1, Z equals B.
    check_select1_path: assert property (
        @(posedge CLK) disable iff (1'b0) (S == 1'b1) |-> (Z == B)
    );

    // If A and B are equal, Z equals that value regardless of S.
    check_equal_inputs: assert property (
        @(posedge CLK) disable iff (1'b0) (A == B) |-> (Z == A)
    );

    // Z always matches one of the inputs (A or B).
    check_output_matches_one_input: assert property (
        @(posedge CLK) disable iff (1'b0) (Z == A) || (Z == B)
    );
endmodule