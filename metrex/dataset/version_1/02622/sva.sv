// SVA for top_module
module top_module_sva;
  // Accesses DUT signals via bind scope
  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1'b1;

  default disable iff (!past_valid);

  let good = !$isunknown({load, up_down, D, up_counter, down_counter, OUT});

  // Load behavior
  assert property (good && load |=> up_counter == $past(D) && down_counter == $past(D));
  assert property (good && load |=> OUT == 4'h0);

  // Up-counter behavior (increment/wrap) and hold when not enabled
  assert property (good && !load && up_down |=> up_counter == (($past(up_counter)==4'hF) ? 4'h0 : $past(up_counter)+4'h1));
  assert property (good && !load && !up_down |=> up_counter == $past(up_counter));

  // Down-counter behavior (decrement/wrap) and hold when not enabled
  assert property (good && !load && !up_down |=> down_counter == (($past(down_counter)==4'h0) ? 4'hF : $past(down_counter)-4'h1));
  assert property (good && !load && up_down |=> down_counter == $past(down_counter));

  // XOR/output relation
  assert property (good |-> OUT == (up_counter ^ down_counter));

  // Coverage
  cover property (good && load);
  cover property (good && !load && up_down && up_counter==4'hF ##1 up_counter==4'h0);
  cover property (good && !load && !up_down && down_counter==4'h0 ##1 down_counter==4'hF);
  cover property (good && !load && up_down && up_counter!=4'hF ##1 up_counter == $past(up_counter)+4'h1);
  cover property (good && !load && !up_down && down_counter!=4'h0 ##1 down_counter == $past(down_counter)-4'h1);
  cover property (good && OUT != 4'h0);
endmodule

bind top_module top_module_sva sva_inst();