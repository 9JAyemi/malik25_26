module sky130_fd_sc_ls__clkdlyinv3sd2_sva (
    // DUT has no clock/reset; pure combinational inverter (Y = ~A).
    // This checker uses external CLK (posedge) and active-low RESETn for sampling.
    input  logic CLK,
    input  logic RESETn,
    input  logic Y,
    input  logic A
);
    // Y equals bitwise NOT of A every cycle.
    check_inversion_value: assert property (
        @(posedge CLK) disable iff (!RESETn) (Y === ~A)
    );

    // A rising edge implies Y fell in the same sample.
    check_riseA_fallY: assert property (
        @(posedge CLK) disable iff (!RESETn) $rose(A) |-> $fell(Y)
    );

    // A falling edge implies Y rose in the same sample.
    check_fallA_riseY: assert property (
        @(posedge CLK) disable iff (!RESETn) $fell(A) |-> $rose(Y)
    );

    // If A is stable between samples, Y must be stable.
    check_stable_A_implies_stable_Y: assert property (
        @(posedge CLK) disable iff (!RESETn) $stable(A) |-> $stable(Y)
    );

    // Any change on A causes a change on Y in the same sample.
    check_change_A_to_Y: assert property (
        @(posedge CLK) disable iff (!RESETn) $changed(A) |-> $changed(Y)
    );

    // Any change on Y implies a change on A in the same sample.
    check_change_Y_to_A: assert property (
        @(posedge CLK) disable iff (!RESETn) $changed(Y) |-> $changed(A)
    );
endmodule