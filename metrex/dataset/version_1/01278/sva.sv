// SVA checkers and binds for top_module and its submodules

// Checker for add_overflow_detection (binds to every instance)
module aod_sva (
  input logic [7:0] a,
  input logic [7:0] b,
  input logic [7:0] s,
  input logic       overflow
);
  default clocking cb @(*); endclocking

  // Functional correctness
  assert property ( s == ({1'b0,a}+{1'b0,b})[7:0] );
  assert property ( overflow == ({1'b0,a}+{1'b0,b})[8] );

  // X-prop hygiene
  assert property ( !$isunknown({a,b}) |=> !$isunknown({s,overflow}) );

  // Useful coverage
  cover property ( overflow );
  cover property ( !overflow );
  cover property ( (a==8'hFF) && (b==8'h01) && overflow );
  cover property ( (a==8'h00) && (b==8'h00) && !overflow );
endmodule

// Checker for byte_splitter (binds to every instance)
module bs_sva (
  input logic [15:0] in,
  input logic [7:0]  out_hi,
  input logic [7:0]  out_lo
);
  default clocking cb @(*); endclocking

  // Bit slicing correctness
  assert property ( out_hi == in[15:8] );
  assert property ( out_lo == in[7:0] );

  // X-prop hygiene
  assert property ( !$isunknown(in) |=> !$isunknown({out_hi,out_lo}) );

  // Coverage
  cover property ( in==16'h0000 );
  cover property ( in==16'hFFFF );
endmodule

// Top-level checker (binds into top_module) to verify connectivity and end-to-end intent
module top_module_sva (
  input logic [15:0] in,
  input logic [7:0]  a,
  input logic [7:0]  b,
  input logic [7:0]  upper_byte,
  input logic [7:0]  lower_byte,
  input logic [7:0]  sum,
  input logic        overflow,
  input logic [7:0]  out
);
  default clocking cb @(*); endclocking

  // Byte splitter correctness (duplicate of bs_sva but ensures top-level nets are wired correctly)
  assert property ( upper_byte == in[15:8] );
  assert property ( lower_byte == in[7:0] );

  // Connectivity checks to sub-instances
  assert property ( aod_upper.a == a && aod_upper.b == upper_byte );
  assert property ( aod_lower.a == b && aod_lower.b == lower_byte );
  assert property ( out == sum );
  assert property ( sum == aod_upper.s && overflow == aod_upper.overflow );

  // End-to-end function for the visible path
  assert property ( sum == ({1'b0,a}+{1'b0,upper_byte})[7:0] );
  assert property ( overflow == ({1'b0,a}+{1'b0,upper_byte})[8] );
  assert property ( out == ({1'b0,a}+{1'b0,in[15:8]})[7:0] );

  // X-prop hygiene at top
  assert property ( !$isunknown({in,a,b}) |=> !$isunknown({upper_byte,lower_byte,sum,overflow,out}) );

  // Coverage on the visible path
  cover property ( overflow );
  cover property ( !overflow );
  cover property ( (a==8'hFF) && (upper_byte==8'h01) && overflow );
  cover property ( (a==8'h00) && (upper_byte==8'h00) && !overflow );
endmodule

// Bind the checkers
bind add_overflow_detection aod_sva aod_sva_i (.*);
bind byte_splitter         bs_sva  bs_sva_i  (.*);
bind top_module            top_module_sva tmsva (.*);