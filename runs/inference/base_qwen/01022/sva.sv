module sky130_fd_sc_lp__or2_sva (
    input logic CLK,
    input logic A,
    input logic B,
    output logic X
);
    // The OR gate output X is the result of A OR B.
    or_behavior: assert property (
        @(posedge CLK) $stable(A) |-> $stable(B) |-> (X == (A | B))
    );
endmodule