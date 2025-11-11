// SVA checkers for byte_counter and its submodules.
// Assumes sampling on $global_clock.

module byte_counter_sva (
  input logic [15:0] in,
  input logic [7:0]  in_vec,
  input logic [7:0]  out,
  input logic [7:0]  upper_byte,
  input logic [7:0]  lower_byte,
  input logic [7:0]  upper_count,
  input logic [7:0]  lower_count,
  input logic [7:0]  vec_count,
  input logic [8:0]  sum
);
  default clocking cb @(posedge $global_clock); endclocking

  function automatic [3:0] pop8(input logic [7:0] v);
    pop8 = $countones(v);
  endfunction

  // Structural split is correct
  assert property (upper_byte == in[15:8]);
  assert property (lower_byte == in[7:0]);

  // Each “counter” output must be an 8-bit popcount (0..8)
  assert property (upper_count == pop8(upper_byte));
  assert property (lower_count == pop8(lower_byte));
  assert property (vec_count   == pop8(in_vec));
  assert property (upper_count <= 8);
  assert property (lower_count <= 8);
  assert property (vec_count   <= 8);

  // Adder correctness and range (sum of three popcounts fits in 9 bits, <=24)
  assert property (sum == ({1'b0,upper_count}+{1'b0,lower_count}+{1'b0,vec_count}));
  assert property (sum[8] == 1'b0);  // max is 24

  // Output is LSB of sum and matches end-to-end spec
  assert property (out == sum[7:0]);
  assert property (out == ({1'b0,pop8(upper_byte)}+{1'b0,pop8(lower_byte)}+{1'b0,pop8(in_vec)})[7:0]);
  assert property (out <= 8'd24);

  // X-propagation hygiene
  assert property (!$isunknown({in,in_vec}) |-> !$isunknown({upper_byte,lower_byte,upper_count,lower_count,vec_count,sum,out}));

  // Concise functional coverage
  cover property (in==16'h0000 && in_vec==8'h00 && out==8'd0);
  cover property (in==16'hFFFF && in_vec==8'hFF && out==8'd24);
  cover property (upper_byte==8'hFF && lower_byte==8'h00 && in_vec==8'h00 && out==8'd8);
  cover property (upper_byte==8'h00 && lower_byte==8'hFF && in_vec==8'h00 && out==8'd8);
  cover property (upper_byte==8'h00 && lower_byte==8'h00 && in_vec==8'hFF && out==8'd8);
  cover property (pop8(upper_byte)==4 && pop8(lower_byte)==4 && pop8(in_vec)==4 && out==8'd12);
endmodule

module barrel_shifter_sva (
  input logic [7:0] in,
  input logic [7:0] out
);
  default clocking cb @(posedge $global_clock); endclocking
  function automatic [3:0] pop8(input logic [7:0] v);
    pop8 = $countones(v);
  endfunction
  // Must behave as a popcount (as used/claimed)
  assert property (out == pop8(in));
  assert property (out <= 8);
  assert property (!$isunknown(in) |-> !$isunknown(out));
  // Coverage
  cover property (in==8'h00 && out==0);
  cover property (in==8'hFF && out==8);
  cover property (in==8'h01 && out==1);
  cover property (in==8'h80 && out==1);
endmodule

module binary_tree_adder_sva (
  input logic [23:0] in,
  input logic [8:0]  out
);
  default clocking cb @(posedge $global_clock); endclocking
  // Must equal sum of the three bytes
  assert property (out == {1'b0,in[23:16]} + {1'b0,in[15:8]} + {1'b0,in[7:0]});
  assert property (!$isunknown(in) |-> !$isunknown(out));
  // Coverage (general adder behavior)
  cover property (in==24'h000000 && out==0);
  cover property (in==24'hFF0000 && out==255);
  cover property (in==24'h00FF00 && out==255);
  cover property (in==24'h0000FF && out==255);
endmodule

// Bind checkers into DUTs
bind byte_counter       byte_counter_sva      u_byte_counter_sva( .in(in), .in_vec(in_vec), .out(out), .upper_byte(upper_byte), .lower_byte(lower_byte), .upper_count(upper_count), .lower_count(lower_count), .vec_count(vec_count), .sum(sum) );
bind barrel_shifter     barrel_shifter_sva    u_barrel_shifter_sva( .in(in), .out(out) );
bind binary_tree_adder  binary_tree_adder_sva u_binary_tree_adder_sva( .in(in), .out(out) );