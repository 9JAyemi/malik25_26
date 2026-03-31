module digital_circuit_sva (
    input logic D,
    input logic Q,
    input logic Q_N,
    input logic SCD,
    input logic SCE,
    input logic CLK,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);

// Q captures SCE ? SCD : D on the next clock.
    check_q_captures_muxed_input: assert property (
        @(posedge CLK) 1'b1 |=> (Q == ($past(SCE) ? $past(SCD) : $past(D)))
    );

// Q_N is the complement of Q on the next clock.
    check_qn_complements_q: assert property (
        @(posedge CLK) 1'b1 |=> (Q_N == ~Q)
    );

// With SCE low, Q captures D on the next clock.
    check_q_captures_d_when_sce_low: assert property (
        @(posedge CLK) !SCE |=> (Q == $past(D))
    );

// With SCE high, Q captures SCD on the next clock.
    check_q_captures_scd_when_sce_high: assert property (
        @(posedge CLK) SCE |=> (Q == $past(SCD))
    );

// A rising edge on SCE causes Q to capture SCD on the next clock.
    check_q_captures_scd_on_sce_rise: assert property (
        @(posedge CLK) $rose(SCE) |=> (Q == $past(SCD))
    );

// A falling edge on SCE causes Q to capture D on the next clock.
    check_q_captures_d_on_sce_fall: assert property (
        @(posedge CLK) $fell(SCE) |=> (Q == $past(D))
    );

// A rising edge on SCD causes Q to capture SCD on the next clock when SCE is high.
    check_q_captures_scd_on_scd_rise_when_sce_high: assert property (
        @(posedge CLK) SCE && $rose(SCD) |=> (Q == $past(SCD))
    );

// A falling edge on SCD causes Q to capture D on the next clock when SCE is high.
    check_q_captures_d_on_scd_fall_when_sce_high: assert property (
        @(posedge CLK) SCE && $fell(SCD) |=> (Q == $past(D))
    );

endmodule
