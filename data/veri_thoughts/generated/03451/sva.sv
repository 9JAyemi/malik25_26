module mux8to1_assertions (
    input logic [7:0] A,
    input logic [2:0] S,
    input logic X
);

    // No RTL clock or reset; sample the combinational mux on the global formal clock.

    // S=000 selects A[0].
    check_select_0: assert property (
        @($global_clock) (S == 3'b000) |-> (X == A[0])
    );

    // S=001 selects A[1].
    check_select_1: assert property (
        @($global_clock) (S == 3'b001) |-> (X == A[1])
    );

    // S=010 selects A[2].
    check_select_2: assert property (
        @($global_clock) (S == 3'b010) |-> (X == A[2])
    );

    // S=011 selects A[3].
    check_select_3: assert property (
        @($global_clock) (S == 3'b011) |-> (X == A[3])
    );

    // S=100 selects A[4].
    check_select_4: assert property (
        @($global_clock) (S == 3'b100) |-> (X == A[4])
    );

    // S=101 selects A[5].
    check_select_5: assert property (
        @($global_clock) (S == 3'b101) |-> (X == A[5])
    );

    // S=110 selects A[6].
    check_select_6: assert property (
        @($global_clock) (S == 3'b110) |-> (X == A[6])
    );

    // S=111 selects A[7].
    check_select_7: assert property (
        @($global_clock) (S == 3'b111) |-> (X == A[7])
    );

    // X matches the RTL sum-of-products mux equation.
    check_output_sum_of_products: assert property (
        @($global_clock)
        X == ((~S[2] & ~S[1] & ~S[0] & A[0]) |
              (~S[2] & ~S[1] &  S[0] & A[1]) |
              (~S[2] &  S[1] & ~S[0] & A[2]) |
              (~S[2] &  S[1] &  S[0] & A[3]) |
              ( S[2] & ~S[1] & ~S[0] & A[4]) |
              ( S[2] & ~S[1] &  S[0] & A[5]) |
              ( S[2] &  S[1] & ~S[0] & A[6]) |
              ( S[2] &  S[1] &  S[0] & A[7]))
    );

    // Stable select and selected input keep X stable.
    check_output_stable_when_selected_path_stable: assert property (
        @($global_clock)
        (!$initstate &&
         $stable(S) &&
         (((S == 3'b000) && $stable(A[0])) ||
          ((S == 3'b001) && $stable(A[1])) ||
          ((S == 3'b010) && $stable(A[2])) ||
          ((S == 3'b011) && $stable(A[3])) ||
          ((S == 3'b100) && $stable(A[4])) ||
          ((S == 3'b101) && $stable(A[5])) ||
          ((S == 3'b110) && $stable(A[6])) ||
          ((S == 3'b111) && $stable(A[7]))))
        |-> $stable(X)
    );

    // With stable select, a selected-input change must change X.
    check_output_tracks_selected_input_change: assert property (
        @($global_clock)
        (!$initstate &&
         $stable(S) &&
         (((S == 3'b000) && (A[0] != $past(A[0]))) ||
          ((S == 3'b001) && (A[1] != $past(A[1]))) ||
          ((S == 3'b010) && (A[2] != $past(A[2]))) ||
          ((S == 3'b011) && (A[3] != $past(A[3]))) ||
          ((S == 3'b100) && (A[4] != $past(A[4]))) ||
          ((S == 3'b101) && (A[5] != $past(A[5]))) ||
          ((S == 3'b110) && (A[6] != $past(A[6]))) ||
          ((S == 3'b111) && (A[7] != $past(A[7])))))
        |-> (X != $past(X))
    );

endmodule