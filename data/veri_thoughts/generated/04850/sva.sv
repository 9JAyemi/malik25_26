module karnaugh_map_sva(
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic F
);

    // F is 1 for the four minterms assigned high.
    check_f_high_minterms: assert property (
        @($global_clock) disable iff (1'b0)
        ((({A,B,C,D} === 4'b0000) ||
          ({A,B,C,D} === 4'b0010) ||
          ({A,B,C,D} === 4'b0101) ||
          ({A,B,C,D} === 4'b1001))) |-> (F === 1'b1)
    );

    // F is 0 for the four minterms explicitly assigned low.
    check_f_low_explicit_minterms: assert property (
        @($global_clock) disable iff (1'b0)
        ((({A,B,C,D} === 4'b0001) ||
          ({A,B,C,D} === 4'b0100) ||
          ({A,B,C,D} === 4'b1010) ||
          ({A,B,C,D} === 4'b1111))) |-> (F === 1'b0)
    );

    // F is 0 for every input combination handled by the default case.
    check_f_low_default_minterms: assert property (
        @($global_clock) disable iff (1'b0)
        ((({A,B,C,D} !== 4'b0000) &&
          ({A,B,C,D} !== 4'b0010) &&
          ({A,B,C,D} !== 4'b0101) &&
          ({A,B,C,D} !== 4'b1001) &&
          ({A,B,C,D} !== 4'b0001) &&
          ({A,B,C,D} !== 4'b0100) &&
          ({A,B,C,D} !== 4'b1010) &&
          ({A,B,C,D} !== 4'b1111))) |-> (F === 1'b0)
    );

endmodule