module d_flip_flop_mux_sva (
    input logic clk,
    input logic [7:0] d1,
    input logic [7:0] d2,
    input logic sel,
    input logic [7:0] q
);

// q captures d1 on the next falling edge when sel is low.
    check_capture_d1_when_sel_low: assert property (
        @(negedge clk) !sel |=> (q == $past(d1))
    );

// q captures d2 on the next falling edge when sel is high.
    check_capture_d2_when_sel_high: assert property (
        @(negedge clk) sel |=> (q == $past(d2))
    );

// q holds its value on the next falling edge when d_in is stable.
    check_hold_when_d_in_stable: assert property (
        @(negedge clk) 1'b1 |=> ((d1 == $past(d1)) && (d2 == $past(d2)) && (sel == $past(sel))) |-> (q == $past(q))
    );

endmodule
