module karnaugh_map_sva(
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic F
);

    // F must match the RTL truth table on every sampled cycle.
    check_function_matches_truth_table: assert property (
        @(posedge clk) F == (B ^ C ^ D)
    );

    // If only A changes between samples, F must stay the same.
    check_a_only_change_keeps_f_stable: assert property (
        @(posedge clk) !$initstate && $changed(A) && $stable(B) && $stable(C) && $stable(D) |-> $stable(F)
    );

    // If only B changes between samples, F must toggle.
    check_b_only_change_toggles_f: assert property (
        @(posedge clk) !$initstate && $stable(A) && $changed(B) && $stable(C) && $stable(D) |-> $changed(F)
    );

    // If only C changes between samples, F must toggle.
    check_c_only_change_toggles_f: assert property (
        @(posedge clk) !$initstate && $stable(A) && $stable(B) && $changed(C) && $stable(D) |-> $changed(F)
    );

    // If only D changes between samples, F must toggle.
    check_d_only_change_toggles_f: assert property (
        @(posedge clk) !$initstate && $stable(A) && $stable(B) && $stable(C) && $changed(D) |-> $changed(F)
    );

    // If B, C, and D are unchanged, F must remain unchanged.
    check_bcd_stable_keeps_f_stable: assert property (
        @(posedge clk) !$initstate && $stable(B) && $stable(C) && $stable(D) |-> $stable(F)
    );

endmodule