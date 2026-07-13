module TLU_sva (
    input logic EN,
    input logic SE,
    input logic CK,
    input logic Q
);

    // Q holds its value when the enable input is low.
    check_hold_when_disabled: assert property (
        @(posedge CK) !EN |=> (Q == $past(Q))
    );

    // Q captures SE when the enable input is high.
    check_capture_when_enabled: assert property (
        @(posedge CK) EN |=> (Q == $past(SE))
    );

endmodule