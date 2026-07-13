module xor4_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic X
);

    // X matches the XOR tree implemented in xor4.
    check_output_matches_xor_tree: assert property (
        @(posedge clk) disable iff ($initstate)
        X == ((A ^ B) ^ (C ^ D))
    );

    // An odd number of sampled input toggles makes X toggle.
    check_output_toggles_on_odd_input_toggle_parity: assert property (
        @(posedge clk) disable iff ($initstate)
        (((A ^ $past(A)) ^ (B ^ $past(B)) ^ (C ^ $past(C)) ^ (D ^ $past(D))) == 1'b1)
        |-> (X != $past(X))
    );

    // An even number of sampled input toggles keeps X unchanged.
    check_output_stable_on_even_input_toggle_parity: assert property (
        @(posedge clk) disable iff ($initstate)
        (((A ^ $past(A)) ^ (B ^ $past(B)) ^ (C ^ $past(C)) ^ (D ^ $past(D))) == 1'b0)
        |-> (X == $past(X))
    );

endmodule