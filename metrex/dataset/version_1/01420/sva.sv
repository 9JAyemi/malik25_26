// SVA for up_down_counter
module up_down_counter_sva (
  input clk, input reset, input enable, input up_down, input [3:0] count
);
  default clocking @(posedge clk); endclocking

  // Reset behavior
  assert property (reset |=> count==4'd0);

  // Known after reset deassert
  assert property (!reset |-> !$isunknown(count));

  // Hold when not enabled
  assert property (!reset && !enable |=> count==$past(count,1,reset));

  // Count up
  assert property (!reset && enable && up_down |=> count==$past(count,1,reset)+4'd1);

  // Count down when > 0
  assert property (!reset && enable && !up_down && $past(count,1,reset)>0
                   |=> count==$past(count,1,reset)-4'd1);

  // Hold at 0 on down
  assert property (!reset && enable && !up_down && $past(count,1,reset)==0
                   |=> count==4'd0);

  // Wrap on increment from 15
  assert property (!reset && enable && up_down && $past(count,1,reset)==4'hF
                   |=> count==4'd0);

  // Coverage
  cover property (reset ##1 !reset ##1 enable && up_down [*2]);
  cover property (!reset && enable && up_down && $past(count,1,reset)==4'hF ##1 count==4'd0);
  cover property (!reset && enable && !up_down && $past(count,1,reset)>0);
  cover property (!reset && !enable ##1 count==$past(count,1,reset));
endmodule

bind up_down_counter up_down_counter_sva up_down_counter_sva_i (.*);


// SVA for shift_register (port-observable)
module shift_register_sva (
  input clk, input reset, input load,
  input [3:0] data_in, input [3:0] data_out
);
  default clocking @(posedge clk); endclocking

  // Reset drives zeros
  assert property (reset |=> data_out==4'd0);

  // Known after reset deassert
  assert property (!reset |-> !$isunknown(data_out));

  // Load behavior
  assert property (!reset && load |=> data_out==$past(data_in,1,reset));

  // "Shift": upper bits hold, LSB becomes 0 when not loading
  assert property (!reset && !load
                   |=> data_out[3:1]==$past(data_out[3:1],1,reset) && data_out[0]==1'b0);

  // Coverage
  cover property (!reset && load ##1 !load);
  cover property (!reset && !load ##1 !load);
endmodule

bind shift_register shift_register_sva shift_register_sva_i (.*);


// SVA for top_module integration
module top_module_sva (
  input clk, input reset, input up_down, input load,
  input [3:0] data_in, input [3:0] data_out
);
  // count and enable are internal to top_module; access by hierarchical names via bind
  // Re-declare to connect via bind's implicit .* to top_module's internal names
  wire [3:0] count;  // will connect through bind by name
  wire enable;

  default clocking @(posedge clk); endclocking

  // Registered enable equals inverted load (one-cycle latency, reset-guarded)
  assert property (!reset |-> enable == !$past(load,1,reset));

  // On load, shift_register captures counter value
  assert property (load |=> data_out == $past(count,1,reset));

  // Reset clears data_out
  assert property (reset |=> data_out==4'd0);

  // Optional coverage: load-capture followed by counting then another capture
  cover property (reset ##1 !reset ##1 load ##1 !load ##1 !load ##1 load);
endmodule

bind top_module top_module_sva top_module_sva_i (.*);