module Datapath_Unit_sva (
    input  logic signed [15:0] CR,
    input  logic AR_gt_0,
    input  logic AR_lt_0,
    input  logic [15:0] Data_AR,
    input  logic [15:0] Data_BR,
    input  logic Ld_AR_BR,
    input  logic Div_AR_x2_CR,
    input  logic Mul_BR_x2_CR,
    input  logic Clr_CR,
    input  logic clk
);
    // AR_gt_0 and AR_lt_0 are never both HIGH simultaneously.
    check_ar_flags_mutex: assert property (
        @(negedge clk) disable iff ($initstate) !(AR_gt_0 && AR_lt_0)
    );

    // AR flags remain stable across cycles if no load in previous and current cycles.
    check_ar_flags_stable_without_load: assert property (
        @(negedge clk) disable iff ($initstate)
            (!$past(Ld_AR_BR) && !Ld_AR_BR) |-> (AR_gt_0 == $past(AR_gt_0) && AR_lt_0 == $past(AR_lt_0))
    );

    // After load with positive Data_AR, AR_gt_0=1 and AR_lt_0=0 at next cycle.
    check_ar_flags_after_load_pos: assert property (
        @(negedge clk) disable iff ($initstate)
            (Ld_AR_BR && ($signed(Data_AR) > 0)) |=> (AR_gt_0 == 1'b1 && AR_lt_0 == 1'b0)
    );

    // After load with negative Data_AR, AR_lt_0=1 and AR_gt_0=0 at next cycle.
    check_ar_flags_after_load_neg: assert property (
        @(negedge clk) disable iff ($initstate)
            (Ld_AR_BR && ($signed(Data_AR) < 0)) |=> (AR_gt_0 == 1'b0 && AR_lt_0 == 1'b1)
    );

    // After load with zero Data_AR, both AR flags are 0 at next cycle.
    check_ar_flags_after_load_zero: assert property (
        @(negedge clk) disable iff ($initstate)
            (Ld_AR_BR && ($signed(Data_AR) == 0)) |=> (AR_gt_0 == 1'b0 && AR_lt_0 == 1'b0)
    );

    // After load with non-zero Data_AR, exactly one AR flag is HIGH at next cycle.
    check_ar_flags_after_load_nonzero_onehot: assert property (
        @(negedge clk) disable iff ($initstate)
            (Ld_AR_BR && ($signed(Data_AR) != 0)) |=> (AR_gt_0 ^ AR_lt_0)
    );

    // Loading AR/BR does not modify CR; CR holds its previous value.
    check_cr_hold_on_load: assert property (
        @(negedge clk) disable iff ($initstate)
            Ld_AR_BR |=> (CR == $past(CR))
    );

    // With no operations asserted, CR holds its previous value.
    check_cr_hold_when_no_ops: assert property (
        @(negedge clk) disable iff ($initstate)
            (!Ld_AR_BR && !Div_AR_x2_CR && !Mul_BR_x2_CR && !Clr_CR) |=> (CR == $past(CR))
    );

    // When only Clr_CR is selected (and Ld/Div/Mul are 0), CR is cleared to 0.
    check_cr_clear_when_only_clr: assert property (
        @(negedge clk) disable iff ($initstate)
            (!Ld_AR_BR && !Div_AR_x2_CR && !Mul_BR_x2_CR && Clr_CR) |=> (CR == 16'sd0)
    );

    // If only Clr_CR is selected in consecutive cycles, CR remains 0.
    check_cr_zero_persistent_on_only_clr: assert property (
        @(negedge clk) disable iff ($initstate)
            ($past(!Ld_AR_BR && !Div_AR_x2_CR && !Mul_BR_x2_CR && Clr_CR) &&
             (!Ld_AR_BR && !Div_AR_x2_CR && !Mul_BR_x2_CR && Clr_CR)) |-> (CR == 16'sd0)
    );

endmodule