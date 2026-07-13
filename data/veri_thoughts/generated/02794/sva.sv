module delay_module_sva (
    input  logic CLK,
    input  logic g,
    input  logic d,
    input  logic s,
    input  logic out,
    // Internal signal from DUT (delay_module.d_delayed)
    input  logic d_delayed
);
    // Out equals delayed data or its inversion based on select s.
    check_out_select_invert: assert property (
        @(posedge CLK) disable iff (1'b0) out == (s ? ~d_delayed : d_delayed)
    );

    // If s and d_delayed are stable, out must be stable.
    check_out_stable_when_inputs_stable: assert property (
        @(posedge CLK) disable iff (1'b0) ($stable(s) && $stable(d_delayed)) |-> $stable(out)
    );

    // If d_delayed changes while s is stable, out must change.
    check_d_change_implies_out_change_when_s_stable: assert property (
        @(posedge CLK) disable iff (1'b0) ($changed(d_delayed) && $stable(s)) |-> $changed(out)
    );

    // If out changes while s is stable, d_delayed must change.
    check_out_change_implies_d_change_when_s_stable: assert property (
        @(posedge CLK) disable iff (1'b0) ($changed(out) && $stable(s)) |-> $changed(d_delayed)
    );

    // If s changes while d_delayed is stable, out must change.
    check_s_change_implies_out_change_when_d_stable: assert property (
        @(posedge CLK) disable iff (1'b0) ($changed(s) && $stable(d_delayed)) |-> $changed(out)
    );

    // If out changes while d_delayed is stable, s must change.
    check_out_change_implies_s_change_when_d_stable: assert property (
        @(posedge CLK) disable iff (1'b0) ($changed(out) && $stable(d_delayed)) |-> $changed(s)
    );
endmodule