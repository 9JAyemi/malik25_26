module dff_en_sva (
    input logic D,
    input logic C,
    input logic E,
    input logic Q
);

// Q captures D on the next clock when E is high.
    check_capture_when_enabled: assert property (
        @(posedge C) E |=> (Q == $past(D))
    );

// Q holds its value on the next clock when E is low.
    check_hold_when_disabled: assert property (
        @(posedge C) !E |=> (Q == $past(Q))
    );

// A high D is captured into Q on the next clock when E is high.
    check_capture_high: assert property (
        @(posedge C) (E && D) |=> (Q == 1'b1)
    );

// A low D is captured into Q on the next clock when E is high.
    check_capture_low: assert property (
        @(posedge C) (E && !D) |=> (Q == 1'b0)
    );

endmodule
