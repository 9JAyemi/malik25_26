module d_ff_sc_ena_set_sva (
    input logic Q,
    input logic CLK,
    input logic D,
    input logic SCD,
    input logic SCE,
    input logic SET_B
);
    // Active-low SET_B forces Q to 0 whenever asserted.
    reset_forces_q0: assert property (
        @(posedge CLK) !SET_B |-> (Q == 1'b0)
    );

    // While SET_B stays low across cycles, Q remains 0.
    reset_holds_q0: assert property (
        @(posedge CLK) (!SET_B && $past(!SET_B)) |-> (Q == 1'b0)
    );

    // With SET_B high, when SCE is 1 load SCD on this clock.
    load_scan_path: assert property (
        @(posedge CLK) disable iff (!SET_B) SCE |=> (Q == $past(SCD))
    );

    // With SET_B high, when SCE is 0 load D on this clock.
    load_func_path: assert property (
        @(posedge CLK) disable iff (!SET_B) !SCE |=> (Q == $past(D))
    );

    // If SCE, SCD, and D are all stable, Q must be stable.
    stable_inputs_hold_q: assert property (
        @(posedge CLK) disable iff (!SET_B) $stable(SCE) && $stable(SCD) && $stable(D) |=> $stable(Q)
    );

    // If SCE is stably 1 and SCD is stable, Q stays stable.
    stable_scan_holds_q: assert property (
        @(posedge CLK) disable iff (!SET_B) SCE && $stable(SCE) && $stable(SCD) |=> $stable(Q)
    );

    // If SCE is stably 0 and D is stable, Q stays stable.
    stable_func_holds_q: assert property (
        @(posedge CLK) disable iff (!SET_B) !SCE && $stable(SCE) && $stable(D) |=> $stable(Q)
    );

    // If D and SCD are equal and both stable, Q takes that common value regardless of SCE.
    equal_inputs_propagate: assert property (
        @(posedge CLK) disable iff (!SET_B) (D == SCD) && $stable(D) && $stable(SCD) |=> (Q == $past(D))
    );
endmodule