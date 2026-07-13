module up_down_counter_assertions (
    input logic       CLK,
    input logic       LOAD,
    input logic       UP,
    input logic       DOWN,
    input logic [3:0] Q
);

    // LOAD overrides the case update and clears Q.
    check_load_clears_q: assert property (
        @(posedge CLK) LOAD |=> (Q == 4'b0000)
    );

    // With LOAD low and UP/DOWN=00, Q decrements.
    check_decrement_on_00: assert property (
        @(posedge CLK) (!LOAD && !UP && !DOWN) |=> (Q == ($past(Q) - 4'd1))
    );

    // With LOAD low and UP/DOWN=01, Q increments.
    check_increment_on_01: assert property (
        @(posedge CLK) (!LOAD && !UP && DOWN) |=> (Q == ($past(Q) + 4'd1))
    );

    // With LOAD low and UP/DOWN=10, Q holds.
    check_hold_on_10: assert property (
        @(posedge CLK) (!LOAD && UP && !DOWN) |=> (Q == $past(Q))
    );

    // With LOAD low and UP/DOWN=11, Q holds.
    check_hold_on_11: assert property (
        @(posedge CLK) (!LOAD && UP && DOWN) |=> (Q == $past(Q))
    );

endmodule