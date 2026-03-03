// SVA checkers and binds for the provided design

// Top-level behavior checker
module top_module_sva (
  input  logic [31:0] a,
  input  logic [31:0] b,
  input  logic        select,
  input  logic [31:0] result
);
  default clocking cb @(a or b or select); endclocking

  // Select=1: result = {31'b0, (a0^b0) & ~a1 & ~b1}
  assert property ( !$isunknown({a[1:0], b[1:0], select}) && select
                    |-> result == {31'b0, ((a[0]^b[0]) & ~a[1] & ~b[1])} );

  // Select=0: result = {30'b0, (a+b)[1:0]}
  assert property ( !$isunknown({a, b, select}) && !select
                    |-> result == {30'b0, (a + b)[1:0]} );

  // Structural zeros on upper bits
  assert property ( !$isunknown({a, b, select})
                    |-> (select ? (result[31:1] == 31'b0)
                                : (result[31:2] == 30'b0)) );

  // Coverage: both modes and LSB=1 in each mode
  cover property (select);
  cover property (!select);
  cover property ( select && (a[1]==0) && (b[1]==0) && (a[0]^b[0]) && result[0] );
  cover property ( !select && ((a + b)[0]) && result[0] );
endmodule

// Subtractor checker (actually adds a+b, returns sum[1:0])
module subtractor_sva (
  input  logic [31:0] a,
  input  logic [31:0] b,
  input  logic [1:0]  result
);
  default clocking cb @(a or b); endclocking

  assert property ( !$isunknown({a, b}) |-> result == (a + b)[1:0] );

  // Coverage of all 2-bit sum outcomes
  cover property (result == 2'b00);
  cover property (result == 2'b01);
  cover property (result == 2'b10);
  cover property (result == 2'b11);
endmodule

// Mux checker (out == (a^b) & ~c & ~d)
module mux_sva (
  input  logic a,
  input  logic b,
  input  logic c,
  input  logic d,
  input  logic out
);
  default clocking cb @(a or b or c or d); endclocking

  assert property ( !$isunknown({a,b,c,d}) |-> out == ((a ^ b) & ~c & ~d) );

  // Coverage
  cover property (out == 1'b1);
  cover property (out == 1'b0);
endmodule

// final_output checker
module final_output_sva (
  input  logic [1:0]  sub_out,
  input  logic        select,
  input  logic        a,
  input  logic        b,
  input  logic        c,
  input  logic        d,
  input  logic [31:0] final_out
);
  default clocking cb @(sub_out or select or a or b or c or d); endclocking

  // Select=0: {30'b0, sub_out}
  assert property ( !$isunknown({sub_out, select}) && !select
                    |-> (final_out[31:2] == 30'b0 && final_out[1:0] == sub_out) );

  // Select=1: {31'b0, (a^b)&~c&~d}
  assert property ( !$isunknown({select, a, b, c, d}) && select
                    |-> final_out == {31'b0, ((a ^ b) & ~c & ~d)} );

  // Coverage
  cover property (!select);
  cover property ( select && ((a ^ b) & ~c & ~d) && final_out[0] );
endmodule

// Bind the SVA to the DUT instances
bind top_module     top_module_sva     top_module_sva_i     (.*);
bind subtractor     subtractor_sva     subtractor_sva_i     (.*);
bind mux            mux_sva            mux_sva_i            (.*);
bind final_output   final_output_sva   final_output_sva_i   (.*);