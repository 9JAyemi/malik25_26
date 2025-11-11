// SVA bind file for barrel_shifter, up_down_counter, bitwise_and
// Concise, high-value checks + coverage

// ---------------- barrel_shifter ----------------
module barrel_shifter_sva (
  input [7:0] data_in,
  input [1:0] shift_amt,
  input       shift_dir,
  input       enable,
  input [7:0] data_out
);
  default clocking cb @(data_in or shift_amt or shift_dir or enable or data_out); endclocking

  // Functional correctness
  assert property (enable && shift_dir    |-> data_out == (data_in << shift_amt));
  assert property (enable && !shift_dir   |-> data_out == (data_in >> shift_amt));
  assert property (!enable                |-> data_out == data_in);
  // Shift-by-0 sanity
  assert property (enable && (shift_amt==2'd0) |-> data_out == data_in);
  // X-prop guards
  assert property (enable |-> !$isunknown({shift_dir,shift_amt}));
  assert property (!$isunknown({data_in,shift_amt,shift_dir,enable}) |-> !$isunknown(data_out));

  // Coverage: both dirs, all shift amounts, enable off, dir toggle
  cover property (enable && shift_dir    && shift_amt==2'd0);
  cover property (enable && shift_dir    && shift_amt==2'd1);
  cover property (enable && shift_dir    && shift_amt==2'd2);
  cover property (enable && shift_dir    && shift_amt==2'd3);
  cover property (enable && !shift_dir   && shift_amt==2'd0);
  cover property (enable && !shift_dir   && shift_amt==2'd1);
  cover property (enable && !shift_dir   && shift_amt==2'd2);
  cover property (enable && !shift_dir   && shift_amt==2'd3);
  cover property (!enable);
  cover property (enable && $changed(shift_dir));
endmodule

bind barrel_shifter barrel_shifter_sva bsh_sva (
  .data_in(data_in), .shift_amt(shift_amt), .shift_dir(shift_dir),
  .enable(enable), .data_out(data_out)
);

// ---------------- up_down_counter ----------------
module up_down_counter_sva (
  input        clk,
  input        rst,
  input        load,
  input        up_down,
  input  [7:0] data_in,
  input  [7:0] data_out,
  input  [7:0] count  // internal reg (white-box)
);
  default clocking cb @(posedge clk); endclocking

  // Priority/functional sequencing
  assert property (rst                    |=> data_out == 8'h00);
  assert property (!rst && load          |=> data_out == data_in);
  assert property (!rst && !load && up_down    |=> data_out == $past(data_out) + 8'd1);
  assert property (!rst && !load && !up_down   |=> data_out == $past(data_out) - 8'd1);
  // Wrap-around
  assert property (!rst && !load && up_down  && $past(data_out)==8'hFF |=> data_out==8'h00);
  assert property (!rst && !load && !up_down && $past(data_out)==8'h00 |=> data_out==8'hFF);
  // Output mirrors internal state
  assert property (1 |-> data_out == count);
  // Knownness when active
  assert property (!rst |-> !$isunknown({load,up_down,data_in}));

  // Coverage: reset, load, up, down, wraps, mode toggle
  cover property (rst);
  cover property (!rst && load);
  cover property (!rst && !load && up_down);
  cover property (!rst && !load && !up_down);
  cover property (!rst && !load && up_down  && $past(data_out)==8'hFF);
  cover property (!rst && !load && !up_down && $past(data_out)==8'h00);
  cover property ($past(!rst && !load) && $changed(up_down));
endmodule

bind up_down_counter up_down_counter_sva udc_sva (
  .clk(clk), .rst(rst), .load(load), .up_down(up_down),
  .data_in(data_in), .data_out(data_out), .count(count)
);

// ---------------- bitwise_and ----------------
module bitwise_and_sva (
  input [7:0] data_in1,
  input [7:0] data_in2,
  input [7:0] data_out
);
  default clocking cb @(data_in1 or data_in2 or data_out); endclocking

  // Functional correctness and X-prop
  assert property (data_out == (data_in1 & data_in2));
  assert property (!$isunknown({data_in1,data_in2}) |-> !$isunknown(data_out));

  // Coverage: key patterns
  cover property (data_in1==8'hFF && data_in2==8'hFF); // all-ones
  cover property (data_in1==8'h00 && data_in2==8'h00); // all-zeros
  cover property (data_in1==8'hFF && data_in2==8'h00); // mask to zero
  cover property (data_in1==8'hAA && data_in2==8'h55); // mixed
endmodule

bind bitwise_and bitwise_and_sva band_sva (
  .data_in1(data_in1), .data_in2(data_in2), .data_out(data_out)
);