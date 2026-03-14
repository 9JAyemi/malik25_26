module mux_2to1_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic SEL,
    input logic Y
);
    // Y must equal the selected input per mux function.
    check_mux_function: assert property (
        @(posedge CLK) disable iff (1'b0) Y == ((SEL == 1'b0) ? A : B)
    );

    // When SEL is 0, Y must equal A.
    check_sel_zero_path: assert property (
        @(posedge CLK) disable iff (1'b0) (SEL == 1'b0) |-> (Y == A)
    );

    // When SEL is 1, Y must equal B.
    check_sel_one_path: assert property (
        @(posedge CLK) disable iff (1'b0) (SEL == 1'b1) |-> (Y == B)
    );

    // Y must always equal one of the inputs.
    check_output_is_one_of_inputs: assert property (
        @(posedge CLK) disable iff (1'b0) (Y == A) || (Y == B)
    );

    // If inputs are equal, Y must equal that common value.
    check_equal_inputs: assert property (
        @(posedge CLK) disable iff (1'b0) (A == B) |-> (Y == A)
    );

    // If inputs differ and Y equals A, SEL must be 0.
    check_select_infers_zero_when_outputs_A: assert property (
        @(posedge CLK) disable iff (1'b0) (A != B && Y == A) |-> (SEL == 1'b0)
    );

    // If inputs differ and Y equals B, SEL must be 1.
    check_select_infers_one_when_outputs_B: assert property (
        @(posedge CLK) disable iff (1'b0) (A != B && Y == B) |-> (SEL == 1'b1)
    );

    // With SEL=0, Y can equal B only if A equals B.
    check_no_bypass_when_sel_zero: assert property (
        @(posedge CLK) disable iff (1'b0) (SEL == 1'b0 && (Y == B)) |-> (A == B)
    );

    // With SEL=1, Y can equal A only if A equals B.
    check_no_bypass_when_sel_one: assert property (
        @(posedge CLK) disable iff (1'b0) (SEL == 1'b1 && (Y == A)) |-> (A == B)
    );
endmodule