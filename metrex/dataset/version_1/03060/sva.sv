// SVA for up_down_counter_4bit
module up_down_counter_4bit_sva
(
  input logic        clk,
  input logic        up_down,
  input logic        load,
  input logic        en,
  input logic [3:0]  data_in,
  input logic [3:0]  out
);

  default clocking cb @(posedge clk); endclocking

  // No-glitch between clocks (output only updates on posedge)
  assert property (@(negedge clk) $stable(out));

  // Hold when disabled
  property p_hold_when_disabled;
    var logic [3:0] v;
    (!en, v = out) |=> out == v;
  endproperty
  assert property (p_hold_when_disabled);

  // Load has priority when enabled
  property p_load;
    var logic [3:0] di;
    (en && load, di = data_in) |=> out == di;
  endproperty
  assert property (p_load);

  // Count up when enabled, not loading
  property p_count_up;
    var logic [3:0] v;
    (en && !load && up_down, v = out) |=> out == v + 4'd1;
  endproperty
  assert property (p_count_up);

  // Count down when enabled, not loading
  property p_count_down;
    var logic [3:0] v;
    (en && !load && !up_down, v = out) |=> out == v - 4'd1;
  endproperty
  assert property (p_count_down);

  // Any change must be due to prior en==1
  property p_change_only_when_en;
    var logic [3:0] v;
    var logic       prev_en;
    (1'b1, v = out, prev_en = en) |=> ((out != v) |-> prev_en);
  endproperty
  assert property (p_change_only_when_en);

  // Inputs known when used
  assert property (en && load      |-> !$isunknown(data_in));
  assert property (en && !load     |-> !$isunknown(up_down));

  // Functional coverage
  cover property (en && load);
  cover property (en && !load && up_down);
  cover property (en && !load && !up_down);

  property p_wrap_up;
    var logic [3:0] v;
    (en && !load && up_down, v = out) |=> (v == 4'hF && out == 4'h0);
  endproperty
  cover property (p_wrap_up);

  property p_wrap_down;
    var logic [3:0] v;
    (en && !load && !up_down, v = out) |=> (v == 4'h0 && out == 4'hF);
  endproperty
  cover property (p_wrap_down);

endmodule

bind up_down_counter_4bit up_down_counter_4bit_sva sva_inst
(
  .clk(clk),
  .up_down(up_down),
  .load(load),
  .en(en),
  .data_in(data_in),
  .out(out)
);