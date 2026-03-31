module RegisterAdd__parameterized5_sva (
    input logic [22:0] Q,
    input logic [0:0] E,
    input logic [22:0] D,
    input logic CLK,
    input logic [0:0] AR
);

// Clock: CLK (posedge). Reset: AR active-low, asynchronous.
    // Logic: sequential with asynchronous reset; Q is registered with add-on-e condition.

    // When AR is LOW at a clock edge, Q becomes zero on the next clock.
    check_async_reset_clears_q: assert property (
        @(posedge CLK) !AR |=> (Q == 23'b0)
    );

// When E is HIGH and D is zero, Q holds its value on the next clock.
    check_hold_when_e_high_d_zero: assert property (
        @(posedge CLK) disable iff (!AR) (E && (D == 23'b0)) |=> (Q == $past(Q))
    );

// When E is HIGH and D is nonzero, Q increments by D modulo 2^23 on the next clock.
    check_increment_when_e_high_d_nonzero: assert property (
        @(posedge CLK) disable iff (!AR) (E && (D != 23'b0)) |=> (Q == ($past(Q) + $past(D)) % 23'd8388608)
    );

// When E is LOW, Q holds its value on the next clock.
    check_hold_when_e_low: assert property (
        @(posedge CLK) disable iff (!AR) (!E) |=> (Q == $past(Q))
    );

endmodule
