// SystemVerilog Assertions for the design

// -------------------- shift_register SVA --------------------
module sr_sva (
  input logic        clk,
  input logic [3:0]  data_in,
  input logic        load,
  input logic [3:0]  data_out
);
  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  // Functional checks
  property p_sr_load;
    past_valid && load |=> data_out == $past(data_in);
  endproperty
  assert property (p_sr_load);

  property p_sr_shift;
    past_valid && !load |=> data_out == { $past(data_out)[2:0], 1'b0 };
  endproperty
  assert property (p_sr_shift);

  // No X on output after first edge
  assert property (past_valid |-> !$isunknown(data_out));

  // Coverage
  cover property (past_valid && load);                     // observe load
  cover property (past_valid && !load[*4]);                // 4 consecutive shifts
  cover property (past_valid && load ##1 !load[*4]);       // load followed by shifts
endmodule

// -------------------- binary_counter SVA --------------------
module bc_sva (
  input logic        clk,
  input logic        EN,
  input logic        RST,
  input logic [3:0]  COUNT
);
  bit past_valid;
  always @(posedge clk or negedge RST) if (!RST) past_valid <= 1'b0; else past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  // Reset dominates
  assert property (!RST |-> COUNT == 4'd0);

  // Hold/increment when out of reset
  assert property (RST && !EN && past_valid |=> COUNT == $past(COUNT));
  assert property (RST &&  EN && past_valid |=> COUNT == $past(COUNT) + 4'd1);

  // No X when out of reset
  assert property (RST |-> !$isunknown(COUNT));

  // Coverage
  cover property (RST && EN && past_valid && $past(COUNT)==4'hF |=> COUNT==4'h0); // wrap
  cover property ($fell(RST));   // async reset asserted
  cover property ($rose(RST));   // reset released
  cover property (RST && EN);    // enabled counting
endmodule

// -------------------- top-level integration SVA --------------------
module top_sva (
  input logic        clk,
  input logic [3:0]  data_out,
  input logic [3:0]  COUNT,
  input logic [7:0]  final_output,
  input logic [7:0]  concat_output
);
  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  // Data-path integrity
  assert property (final_output == {COUNT, data_out});
  assert property (final_output == concat_output);

  // In this design RST is tied low inside top, so COUNT must be zero
  assert property (COUNT == 4'd0);
  assert property (final_output[7:4] == 4'd0);

  // No X on visible signals after first edge
  assert property (past_valid |-> !$isunknown({data_out, COUNT, final_output, concat_output}));

  // Coverage: observe activity on datapath
  cover property (past_valid && $changed(data_out));
  cover property (past_valid && final_output == {COUNT, data_out});
endmodule

// -------------------- Binds --------------------
bind shift_register sr_sva sr_sva_i(.clk(clk), .data_in(data_in), .load(load), .data_out(data_out));
bind binary_counter bc_sva bc_sva_i(.clk(clk), .EN(EN), .RST(RST), .COUNT(COUNT));
bind top_module     top_sva top_sva_i(.clk(clk), .data_out(data_out), .COUNT(COUNT), .final_output(final_output), .concat_output(concat_output));