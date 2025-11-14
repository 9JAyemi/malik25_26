// Add inside jt12_lfo (e.g., under `ifdef SVA or synthesis translate_off)
`ifndef JT12_LFO_SVA
`define JT12_LFO_SVA
// synthesis translate_off

default clocking cb @(posedge clk); endclocking

// Helper: expected limit from lfo_freq
function automatic [6:0] exp_limit(input [2:0] f);
  case (f)
    3'd0: exp_limit = 7'd108;
    3'd1: exp_limit = 7'd77;
    3'd2: exp_limit = 7'd71;
    3'd3: exp_limit = 7'd67;
    3'd4: exp_limit = 7'd62;
    3'd5: exp_limit = 7'd44;
    3'd6: exp_limit = 7'd8;
    3'd7: exp_limit = 7'd5;
  endcase
endfunction

// Safe $past gating
bit pv;
always_ff @(posedge clk) pv <= 1'b1;

// Combinational limit mapping
assert property (limit == exp_limit(lfo_freq));

// Synchronous reset/disable clears state
assert property ((rst || !lfo_en) |-> (lfo_mod == 7'd0 && cnt == 7'd0));

// Hold when not ticking (no clk_en&zero) and enabled
assert property (pv && !rst && lfo_en && !(clk_en && zero)
                 |-> (lfo_mod == $past(lfo_mod) && cnt == $past(cnt)));

// Tick: increment when not at limit
assert property (pv && !rst && lfo_en && clk_en && zero && (cnt != limit)
                 |-> (cnt == $past(cnt) + 7'd1) && (lfo_mod == $past(lfo_mod)));

// Tick: wrap at limit and bump lfo_mod
assert property (pv && !rst && lfo_en && clk_en && zero && (cnt == limit)
                 |-> (cnt == 7'd0) && (lfo_mod == $past(lfo_mod) + 7'd1));

// Stay cleared while lfo_en is low (even if ticking)
assert property (!rst && !lfo_en |-> (lfo_mod == 7'd0 && cnt == 7'd0));

// lfo_mod only changes on tick or reset/disable
assert property (pv && !rst && lfo_en && !(clk_en && zero) |-> $stable(lfo_mod));

// No Xs on state when enabled
assert property (lfo_en |-> !$isunknown({lfo_mod, cnt}));

// ---------------- Coverage ----------------
cover property (rst);
cover property (!rst && lfo_en);                          // enable observed
cover property (clk_en && zero);                          // tick observed
cover property (!clk_en || !zero);                        // no-tick observed
// All freq values exercised
genvar i;
for (i = 0; i < 8; i++) begin : C_FREQ
  cover property (lfo_freq == i[2:0]);
end
// Counter wrap and lfo_mod increment
cover property (!rst && lfo_en && clk_en && zero && (cnt == limit)
                ##1 (cnt == 7'd0));
// lfo_mod overflow wrap (127 -> 0) on wrap tick
cover property (!rst && lfo_en && clk_en && zero && (cnt == limit) && (lfo_mod == 7'h7F)
                ##1 (lfo_mod == 7'd0));

// synthesis translate_on
`endif