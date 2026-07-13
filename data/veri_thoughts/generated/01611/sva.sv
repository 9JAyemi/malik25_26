module decoder_3to8_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic Y0,
    input logic Y1,
    input logic Y2,
    input logic Y3,
    input logic Y4,
    input logic Y5,
    input logic Y6,
    input logic Y7
);
    // Aggregate outputs for compact checks.
    wire [7:0] Y = {Y7, Y6, Y5, Y4, Y3, Y2, Y1, Y0};

    ///// Decoder output invariants /////
    // Outputs are always one-hot (exactly one HIGH).
    check_outputs_onehot: assert property (
        @(posedge A) $onehot(Y)
    );

    // If Y0 is HIGH, all other outputs must be LOW.
    check_y0_mutex: assert property (
        @(posedge A) Y0 |-> !(Y1 || Y2 || Y3 || Y4 || Y5 || Y6 || Y7)
    );
    // If Y1 is HIGH, all other outputs must be LOW.
    check_y1_mutex: assert property (
        @(posedge A) Y1 |-> !(Y0 || Y2 || Y3 || Y4 || Y5 || Y6 || Y7)
    );
    // If Y2 is HIGH, all other outputs must be LOW.
    check_y2_mutex: assert property (
        @(posedge A) Y2 |-> !(Y0 || Y1 || Y3 || Y4 || Y5 || Y6 || Y7)
    );
    // If Y3 is HIGH, all other outputs must be LOW.
    check_y3_mutex: assert property (
        @(posedge A) Y3 |-> !(Y0 || Y1 || Y2 || Y4 || Y5 || Y6 || Y7)
    );
    // If Y4 is HIGH, all other outputs must be LOW.
    check_y4_mutex: assert property (
        @(posedge A) Y4 |-> !(Y0 || Y1 || Y2 || Y3 || Y5 || Y6 || Y7)
    );
    // If Y5 is HIGH, all other outputs must be LOW.
    check_y5_mutex: assert property (
        @(posedge A) Y5 |-> !(Y0 || Y1 || Y2 || Y3 || Y4 || Y6 || Y7)
    );
    // If Y6 is HIGH, all other outputs must be LOW.
    check_y6_mutex: assert property (
        @(posedge A) Y6 |-> !(Y0 || Y1 || Y2 || Y3 || Y4 || Y5 || Y7)
    );
    // If Y7 is HIGH, all other outputs must be LOW.
    check_y7_mutex: assert property (
        @(posedge A) Y7 |-> !(Y0 || Y1 || Y2 || Y3 || Y4 || Y5 || Y6)
    );

    // On any change, the one-hot output can only switch one bit off and one bit on.
    check_transition_two_bits: assert property (
        @(posedge A)
            ($onehot(Y) && $onehot($past(Y))) |-> (($past(Y) == Y) || ($countones(Y ^ $past(Y)) == 2))
    );
endmodule