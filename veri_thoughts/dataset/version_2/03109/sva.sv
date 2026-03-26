module flipflop_assertions (
    input logic C,
    input logic S,
    input logic R,
    input logic T,
    input logic Q
);

    // Clock is C; there is no explicit reset; xorout is combinational and Q updates on C.
    
    // S high and R low force Q high on the next clocked state.
    check_sync_set: assert property (
        @(posedge C) disable iff (1'b0)
        (S == 1'b1 && R == 1'b0) |=> (Q == 1'b1)
    );

    // R high and S low force Q low on the next clocked state.
    check_sync_reset: assert property (
        @(posedge C) disable iff (1'b0)
        (S == 1'b0 && R == 1'b1) |=> (Q == 1'b0)
    );

    // With S and R low, the else path can only use the prior Q or prior T value.
    check_else_low_low_source: assert property (
        @(posedge C) disable iff (1'b0)
        (S == 1'b0 && R == 1'b0) |=> ((Q == $past(Q)) || (Q == $past(T)))
    );

    // With S and R high, the else path can only use the prior Q or prior T value.
    check_else_high_high_source: assert property (
        @(posedge C) disable iff (1'b0)
        (S == 1'b1 && R == 1'b1) |=> ((Q == $past(Q)) || (Q == $past(T)))
    );

    // If the else-path data choices match at a clock edge, Q must retain that value.
    check_equal_sr_matching_data_holds_q: assert property (
        @(posedge C) disable iff (1'b0)
        ((S == R) && (T == Q)) |=> (Q == $past(Q))
    );

endmodule