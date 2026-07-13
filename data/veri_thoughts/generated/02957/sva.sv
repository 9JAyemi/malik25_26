module Span12Mux_v0_sva (
    input logic [11:0] I,
    input logic [3:0]  S,
    input logic [11:0] O
);
    ///// Functional mapping /////
    // For S in 0..11 (S[3:2] != 2'b11), output must pass through input.
    check_passthrough_when_sel_not_11: assert property (
        @(posedge S[0] or posedge S[1] or posedge S[2] or posedge S[3] or
          posedge I[0] or posedge I[1] or posedge I[2] or posedge I[3] or
          posedge I[4] or posedge I[5] or posedge I[6] or posedge I[7] or
          posedge I[8] or posedge I[9] or posedge I[10] or posedge I[11])
        disable iff (1'b0)
        (S[3:2] != 2'b11) |-> (O == I)
    );

    // For S in 12..15 (S[3:2] == 2'b11), output must be all zeros.
    check_zero_when_sel_11xx: assert property (
        @(posedge S[0] or posedge S[1] or posedge S[2] or posedge S[3] or
          posedge I[0] or posedge I[1] or posedge I[2] or posedge I[3] or
          posedge I[4] or posedge I[5] or posedge I[6] or posedge I[7] or
          posedge I[8] or posedge I[9] or posedge I[10] or posedge I[11])
        disable iff (1'b0)
        (S[3:2] == 2'b11) |-> (O == 12'b0)
    );

    ///// Stability expectations for combinational logic /////
    // If S and I are stable, O must remain stable.
    check_stable_on_stable_inputs: assert property (
        @(posedge S[0] or posedge S[1] or posedge S[2] or posedge S[3] or
          posedge I[0] or posedge I[1] or posedge I[2] or posedge I[3] or
          posedge I[4] or posedge I[5] or posedge I[6] or posedge I[7] or
          posedge I[8] or posedge I[9] or posedge I[10] or posedge I[11])
        disable iff (1'b0)
        ($stable(S) && $stable(I)) |-> $stable(O)
    );

    // With selection in 0..11 and S stable, any change on I must be reflected on O.
    check_output_tracks_input_when_selected: assert property (
        @(posedge S[0] or posedge S[1] or posedge S[2] or posedge S[3] or
          posedge I[0] or posedge I[1] or posedge I[2] or posedge I[3] or
          posedge I[4] or posedge I[5] or posedge I[6] or posedge I[7] or
          posedge I[8] or posedge I[9] or posedge I[10] or posedge I[11])
        disable iff (1'b0)
        ((S[3:2] != 2'b11) && $stable(S) && !$stable(I)) |-> (O == I)
    );

    // With selection in 12..15 and S stable, O must remain zero regardless of I changes.
    check_output_ignores_input_when_11xx: assert property (
        @(posedge S[0] or posedge S[1] or posedge S[2] or posedge S[3] or
          posedge I[0] or posedge I[1] or posedge I[2] or posedge I[3] or
          posedge I[4] or posedge I[5] or posedge I[6] or posedge I[7] or
          posedge I[8] or posedge I[9] or posedge I[10] or posedge I[11])
        disable iff (1'b0)
        ((S[3:2] == 2'b11) && $stable(S)) |-> (O == 12'b0)
    );
endmodule