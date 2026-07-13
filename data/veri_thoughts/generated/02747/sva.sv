module decoder_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [15:0] Y
);

    // For known A, Y equals bitwise NOT of (1 << A).
    check_decode_map: assert property (
        @(posedge CLK) (!$isunknown(A)) |-> (Y == ~(16'h0001 << A))
    );

    // For unknown A (X/Z), Y drives all ones via default.
    check_default_on_unknown_A: assert property (
        @(posedge CLK) $isunknown(A) |-> (Y == 16'hFFFF)
    );

    // For known A, ~Y is one-hot (exactly one bit set).
    check_onehot_zero: assert property (
        @(posedge CLK) (!$isunknown(A)) |-> $onehot(~Y)
    );

    // For known A, the selected bit Y[A] is 0.
    check_selected_bit_zero: assert property (
        @(posedge CLK) (!$isunknown(A)) |-> (Y[A] == 1'b0)
    );

    // For known A, Y is not all ones.
    check_not_all_ones_when_known: assert property (
        @(posedge CLK) (!$isunknown(A)) |-> (Y != 16'hFFFF)
    );

    // For known A, Y contains no X/Z.
    check_y_known_when_a_known: assert property (
        @(posedge CLK) (!$isunknown(A)) |-> (!$isunknown(Y))
    );

    // If A is stable between cycles (and known), Y is also stable.
    check_stability_when_a_stable: assert property (
        @(posedge CLK) (!$isunknown(A) && $stable(A)) |-> $stable(Y)
    );

    // For known A, OR-ing Y with the A-bit mask yields all ones (others are 1).
    check_masking_behavior: assert property (
        @(posedge CLK) (!$isunknown(A)) |-> ((Y | (16'h0001 << A)) == 16'hFFFF)
    );

endmodule