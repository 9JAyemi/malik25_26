module d_ff_asynchronous_set_assertions (
    input logic D,
    input logic CLK,
    input logic SET,
    input logic NOTIFIER,
    input logic Q
);

    // Active-low SET must drive Q high by the next clock edge.
    check_set_forces_high_by_next_clk: assert property (
        @(posedge CLK) (!SET) |=> (Q == 1'b1)
    );

    // With SET inactive, capturing D=1 must make Q high on the next clock.
    check_capture_one_when_enabled: assert property (
        @(posedge CLK) disable iff (!SET) (NOTIFIER && D) |=> (Q == 1'b1)
    );

    // With SET inactive, Q=1 must hold when capture is disabled.
    check_hold_high_when_notifier_low: assert property (
        @(posedge CLK) disable iff (!SET) (!NOTIFIER && (Q == 1'b1)) |=> (Q == 1'b1)
    );

    // With SET inactive, Q=1 cannot clear when D is also 1.
    check_high_preserved_when_d_high: assert property (
        @(posedge CLK) disable iff (!SET) ((Q == 1'b1) && (D == 1'b1)) |=> (Q == 1'b1)
    );

endmodule