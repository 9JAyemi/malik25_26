module TLU_sva (
    input logic EN,
    input logic SE,
    input logic CK,
    input logic Q
);

// Q captures SE on the next clock when EN is high.
    check_capture_when_en: assert property (
        @(posedge CK) EN |=> (Q == $past(SE))
    );

// Q holds its value on the next clock when EN is low.
    check_hold_when_en_low: assert property (
        @(posedge CK) !EN |=> (Q == $past(Q))
    );

// Q reflects the previous cycle's SE value when EN is high.
    check_q_matches_prev_se_when_en: assert property (
        @(posedge CK) EN |=> (Q == $past(SE))
    );

// Q reflects the previous cycle's Q value when EN is low.
    check_q_matches_prev_q_when_en_low: assert property (
        @(posedge CK) !EN |=> (Q == $past(Q))
    );

endmodule
