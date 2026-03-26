module shift_reg_assertions (
    input logic        CK,
    input logic        S,
    input logic [3:0]  D,
    input logic [3:0]  Q
);

    // Q updates each cycle from either D or the rotated previous Q.
    check_state_update: assert property (
        @(posedge CK)
        1'b1 |=> Q == ($past(S) ? $past(D) : {$past(Q[2:0]), $past(Q[3])})
    );

    // When S is high, Q loads D.
    check_load_on_select: assert property (
        @(posedge CK)
        S |=> Q == $past(D)
    );

    // When S is low, Q rotates left by one bit.
    check_rotate_on_shift: assert property (
        @(posedge CK)
        !S |=> Q == {$past(Q[2:0]), $past(Q[3])}
    );

    // In shift mode, Q[3] comes from the previous Q[2].
    check_rotate_bit3: assert property (
        @(posedge CK)
        !S |=> Q[3] == $past(Q[2])
    );

    // In shift mode, Q[2] comes from the previous Q[1].
    check_rotate_bit2: assert property (
        @(posedge CK)
        !S |=> Q[2] == $past(Q[1])
    );

    // In shift mode, Q[1] comes from the previous Q[0].
    check_rotate_bit1: assert property (
        @(posedge CK)
        !S |=> Q[1] == $past(Q[0])
    );

    // In shift mode, Q[0] comes from the previous Q[3].
    check_rotate_bit0: assert property (
        @(posedge CK)
        !S |=> Q[0] == $past(Q[3])
    );

    // Four consecutive shifts restore the original value.
    check_four_shifts_restore_state: assert property (
        @(posedge CK)
        (!S)[*4] |=> Q == $past(Q, 4)
    );

endmodule