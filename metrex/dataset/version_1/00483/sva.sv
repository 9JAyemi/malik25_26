// SVA for mux_4to1_enable
// Concise, bindable, with full functional checks and coverage

module mux_4to1_enable_sva (
  input logic [3:0] in,
  input logic [1:0] sel,
  input logic       enable,
  input logic       out
);

  // Sample on any activity; use ##0 to evaluate after combinational settle
  default clocking cb @ (in or sel or enable or out); endclocking

  function automatic logic exp_out (logic [3:0] din, logic [1:0] s, logic en);
    if (!en)                     return 1'b0;
    else if (s === 2'b00)        return din[0];
    else if (s === 2'b01)        return din[1];
    else if (s === 2'b10)        return din[2];
    else if (s === 2'b11)        return din[3];
    else                         return 1'b0; // default on X/Z sel
  endfunction

  // Golden truth-table check (strong 4-state compare)
  property p_truth;
    1'b1 |-> ##0 (out === exp_out(in, sel, enable));
  endproperty
  assert property (p_truth) else $error("mux_4to1_enable: out mismatch with spec");

  // Specific, readable checks (also help pinpoint issues)
  assert property (!enable |-> ##0 (out === 1'b0))
    else $error("mux_4to1_enable: enable=0 must force out=0");

  assert property (enable && (sel === 2'b00) |-> ##0 (out === in[0]))
    else $error("mux_4to1_enable: sel=00 mismatch");
  assert property (enable && (sel === 2'b01) |-> ##0 (out === in[1]))
    else $error("mux_4to1_enable: sel=01 mismatch");
  assert property (enable && (sel === 2'b10) |-> ##0 (out === in[2]))
    else $error("mux_4to1_enable: sel=10 mismatch");
  assert property (enable && (sel === 2'b11) |-> ##0 (out === in[3]))
    else $error("mux_4to1_enable: sel=11 mismatch");

  // Default case on unknown sel while enabled
  assert property (enable && $isunknown(sel) |-> ##0 (out === 1'b0))
    else $error("mux_4to1_enable: X/Z sel must drive out=0 per default");

  // Basic functional coverage
  cover property (enable && (sel === 2'b00) ##0 (out === in[0]));
  cover property (enable && (sel === 2'b01) ##0 (out === in[1]));
  cover property (enable && (sel === 2'b10) ##0 (out === in[2]));
  cover property (enable && (sel === 2'b11) ##0 (out === in[3]));
  cover property (!enable ##0 (out === 1'b0));
  cover property (enable && $isunknown(sel) ##0 (out === 1'b0));

  // Optional: observe enable toggling and selection sweep
  cover property (!enable ##1 enable);
  cover property (enable and (sel inside {2'b00,2'b01,2'b10,2'b11}));

endmodule

// Bind into DUT
bind mux_4to1_enable mux_4to1_enable_sva sva_i (.in(in), .sel(sel), .enable(enable), .out(out));