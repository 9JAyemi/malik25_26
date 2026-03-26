module dff_with_set_reset_sva (
    input logic q,
    input logic qbar,
    input logic clock,
    input logic data,
    input logic PREbar,
    input logic CLRbar
);

    // qbar is always the inverse of q.
    check_qbar_complement: assert property (
        @(posedge clock) disable iff (1'b0)
        qbar == ~q
    );

    // Active-low preset forces q high on the following sampled cycle.
    check_preset_updates_q: assert property (
        @(posedge clock) disable iff (1'b0)
        !$initstate && $past(PREbar == 1'b0) |-> q == 1'b1
    );

    // Active-low clear forces q low when preset was inactive.
    check_clear_updates_q: assert property (
        @(posedge clock) disable iff (1'b0)
        !$initstate && $past(PREbar == 1'b1 && CLRbar == 1'b0) |-> q == 1'b0
    );

    // With preset and clear inactive, q captures data.
    check_data_capture_q: assert property (
        @(posedge clock) disable iff (1'b0)
        !$initstate && $past(PREbar == 1'b1 && CLRbar == 1'b1) |-> q == $past(data)
    );

    // Preset has priority over clear when both are active low.
    check_preset_priority_over_clear: assert property (
        @(posedge clock) disable iff (1'b0)
        !$initstate && $past(PREbar == 1'b0 && CLRbar == 1'b0) |-> q == 1'b1
    );

    // A prior preset cycle drives qbar low.
    check_preset_updates_qbar: assert property (
        @(posedge clock) disable iff (1'b0)
        !$initstate && $past(PREbar == 1'b0) |-> qbar == 1'b0
    );

    // A prior clear cycle drives qbar high when preset was inactive.
    check_clear_updates_qbar: assert property (
        @(posedge clock) disable iff (1'b0)
        !$initstate && $past(PREbar == 1'b1 && CLRbar == 1'b0) |-> qbar == 1'b1
    );

endmodule