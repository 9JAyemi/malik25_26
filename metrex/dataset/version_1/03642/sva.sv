// SVA for top_module
// Bindable checker module (connects to internal nets via bind)
module top_module_sva (
  input  logic         clk,
  input  logic         areset,
  input  logic  [7:0]  d,
  input  logic         sel,
  input  logic         load,
  input  logic         ena,
  input  logic  [3:0]  data,
  input  logic  [7:0]  q,
  input  logic  [7:0]  dff_q,
  input  logic  [3:0]  shift_reg,
  input  logic  [3:0]  mux_out,
  input  logic  [7:0]  xor_out
);

  // Async reset takes effect immediately
  assert property (@(posedge areset) ##0 (q==8'h00 && shift_reg==4'h0 && dff_q==8'h00))
    else $error("Async reset did not drive regs low immediately");

  // While reset held, state remains 0
  assert property (@(posedge clk) areset |-> (q==8'h00 && shift_reg==4'h0));
  assert property (@(negedge clk) areset |-> (dff_q==8'h00));

  // dff_q: rotate halves on each negedge (when not in reset)
  assert property (@(negedge clk) disable iff (areset)
                   $past(!areset) |-> dff_q == { $past(dff_q)[3:0], $past(dff_q)[7:4] })
    else $error("dff_q rotation mismatch");

  // Mux correctness (selected nibble)
  assert property (@(posedge clk or negedge clk) disable iff (areset)
                   mux_out == (sel ? dff_q[7:4] : dff_q[3:0]))
    else $error("mux_out != selected dff_q half");

  // shift_reg next-state behavior and priority: load > ena > hold
  assert property (@(posedge clk) disable iff (areset)
                   $past(!areset && load) |-> shift_reg == $past(data))
    else $error("shift_reg load mismatch");

  assert property (@(posedge clk) disable iff (areset)
                   $past(!areset && !load && ena) |-> shift_reg == {1'b0, $past(shift_reg)[3:1]})
    else $error("shift_reg shift mismatch");

  assert property (@(posedge clk) disable iff (areset)
                   $past(!areset && !load && !ena) |-> shift_reg == $past(shift_reg))
    else $error("shift_reg hold mismatch");

  // q next-state: zero-extended XOR of shift_reg and mux_out
  assert property (@(posedge clk) disable iff (areset)
                   $past(!areset) |-> q == {4'h0, ($past(shift_reg) ^ $past(mux_out))})
    else $error("q next-state mismatch");

  // Optionally check xor_out wiring matches the intent (width extension)
  assert property (@(posedge clk or negedge clk) disable iff (areset)
                   (xor_out[3:0] == (shift_reg ^ mux_out)) && (xor_out[7:4] == 4'h0))
    else $error("xor_out mismatch");

  // No X/Z on key regs when not in reset
  assert property (@(posedge clk) !areset |-> !$isunknown({q, shift_reg}))
    else $error("X/Z detected on posedge domain regs");
  assert property (@(negedge clk) !areset |-> !$isunknown(dff_q))
    else $error("X/Z detected on negedge domain regs");

  // -------------------
  // Coverage (concise)
  // -------------------
  cover property (@(posedge clk) !areset && load);
  cover property (@(posedge clk) !areset && !load && ena);
  cover property (@(posedge clk) !areset && !load && !ena);
  cover property (@(posedge clk) !areset && sel==1'b0);
  cover property (@(posedge clk) !areset && sel==1'b1);
  cover property (@(posedge clk) !areset && load && ena);       // priority scenario
  cover property (@(posedge clk) !areset && q[3:0] != 4'h0);     // XOR effect observed
  cover property (@(negedge clk) !areset);                       // observe negedge activity

endmodule

// Bind into DUT (connect internal nets)
bind top_module top_module_sva sva_i (
  .clk       (clk),
  .areset    (areset),
  .d         (d),
  .sel       (sel),
  .load      (load),
  .ena       (ena),
  .data      (data),
  .q         (q),
  .dff_q     (dff_q),
  .shift_reg (shift_reg),
  .mux_out   (mux_out),
  .xor_out   (xor_out)
);