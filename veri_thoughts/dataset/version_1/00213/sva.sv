module dff_sva #(
    parameter INIT = 1'b0
) (
    input logic Q,
    input logic D,
    input logic C,
    input logic E,
    input logic R,
    input logic S
);

    // Active-low synchronous reset loads INIT.
    check_reset_loads_init: assert property (
        @(posedge C) !R |=> (Q == INIT)
    );

    // Active-low set forces Q high when reset is inactive.
    check_set_forces_one: assert property (
        @(posedge C) disable iff (!R) !S |=> Q
    );

    // With set inactive, enable loads a 0 from D.
    check_enable_loads_zero: assert property (
        @(posedge C) disable iff (!R) (S && E && !D) |=> !Q
    );

    // With set inactive, enable loads a 1 from D.
    check_enable_loads_one: assert property (
        @(posedge C) disable iff (!R) (S && E && D) |=> Q
    );

    // With reset/set inactive and enable low, Q holds 0.
    check_hold_zero_when_disabled: assert property (
        @(posedge C) disable iff (!R) (S && !E && !Q) |=> !Q
    );

    // With reset/set inactive and enable low, Q holds 1.
    check_hold_one_when_disabled: assert property (
        @(posedge C) disable iff (!R) (S && !E && Q) |=> Q
    );

endmodule