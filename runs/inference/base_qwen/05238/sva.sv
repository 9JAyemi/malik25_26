module my_or2_8_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // The logic is purely combinational as there are no sequential elements.

    // The output X is determined by the inputs A, B, and C.
    // When C is HIGH, X is the inverse of the OR of A and B.
    // When C is LOW, X is the OR of A and B.
    combinational_logic: assert property (
        @(posedge VPWR) disable iff (!VGND) (C == 1'b1) |-> (X == ~or(A, B))
    );
    combinational_logic_2: assert property (
        @(posedge VPWR) disable iff (!VGND) (C == 1'b0) |-> (X == or(A, B))
    );

    // The OR gate logic is implemented using a wire.
    // The OR gate is always active as there is no clock.
    or_gate_logic: assert property (
        @(posedge VPWR) disable iff (!VGND) (or_output == A | B)
    );

    // The or_output wire is assigned the result of the OR gate.
    or_output_assignment: assert property (
        @(posedge VPWR) disable iff (!VGND) (or_output == A | B)
    );

    // The X output is assigned based on the value of C and the OR gate result.
    x_assignment: assert property (
        @(posedge VPWR) disable iff (!VGND) (X == (C == 1'b1) ? ~or_output : or_output)
    );

endmodule