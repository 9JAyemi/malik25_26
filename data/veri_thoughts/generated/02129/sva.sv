module d_ff_clear_preset_sva (
    input logic clk,
    input logic d,
    input logic clr,
    input logic preset,
    input logic q,
    input logic q_n
);
    // q_n is always the complement of q.
    outputs_are_complements: assert property (
        @(posedge clk) disable iff (1'b0) (q_n == ~q)
    );

    // q next-state follows priority: clr > preset > d.
    q_next_matches_priority: assert property (
        @(posedge clk) disable iff (1'b0)
            q == ( $past(clr,1,1'b0) ? 1'b0
                 : ($past(preset,1,1'b0) ? 1'b1
                 :  $past(d,1,1'b0) ) )
    );

    // q_n next-state follows priority: clr > preset > ~d.
    qn_next_matches_priority: assert property (
        @(posedge clk) disable iff (1'b0)
            q_n == ( $past(clr,1,1'b0) ? 1'b1
                   : ($past(preset,1,1'b0) ? 1'b0
                   :  ~ $past(d,1,1'b0) ) )
    );

    // If clr was 1 last cycle, outputs are q=0, q_n=1 now.
    clr_forces_clear: assert property (
        @(posedge clk) disable iff (1'b0)
            $past(clr,1,1'b0) |=> (q == 1'b0 && q_n == 1'b1)
    );

    // If preset was 1 and clr was 0 last cycle, outputs are q=1, q_n=0 now.
    preset_sets_when_no_clr: assert property (
        @(posedge clk) disable iff (1'b0)
            (!$past(clr,1,1'b0) && $past(preset,1,1'b0)) |=> (q == 1'b1 && q_n == 1'b0)
    );

    // If neither clr nor preset were 1 last cycle, capture d and ~d now.
    capture_d_when_no_ctrl: assert property (
        @(posedge clk) disable iff (1'b0)
            (!$past(clr,1,1'b0) && !$past(preset,1,1'b0)) |=> (q == $past(d,1,1'b0) && q_n == ~ $past(d,1,1'b0))
    );

    // If both clr and preset were 1 last cycle, clr wins (q=0, q_n=1).
    clr_overrides_preset: assert property (
        @(posedge clk) disable iff (1'b0)
            ($past(clr,1,1'b0) && $past(preset,1,1'b0)) |=> (q == 1'b0 && q_n == 1'b1)
    );
endmodule