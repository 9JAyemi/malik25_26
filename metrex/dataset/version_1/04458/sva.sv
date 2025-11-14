// SVA checkers and bind statements for mux_functional, functional_module, and top_module

// -------------------- mux_functional SVA --------------------
module mux_functional_sva (
  input logic [1:0] in,
  input logic       select,
  input logic [1:0] out
);
  default clocking cb @(
    posedge in[0] or negedge in[0] or
    posedge in[1] or negedge in[1] or
    posedge select or negedge select
  ); endclocking

  // Functional equivalence (mask off X/Z on inputs)
  property p_mux_func;
    disable iff ($isunknown({in,select}))
      out == {1'b0, (select ? in[1] : in[0])};
  endproperty
  assert property (p_mux_func);

  // Upper bit must be 0 due to zero-extension
  property p_out1_zero;
    disable iff ($isunknown({in,select}))
      out[1] == 1'b0;
  endproperty
  assert property (p_out1_zero);

  // Coverage: both selects and both data values
  cover property (!select && (in[0] == 1'b0));
  cover property (!select && (in[0] == 1'b1));
  cover property ( select && (in[1] == 1'b0));
  cover property ( select && (in[1] == 1'b1));

  // Coverage: select toggles
  cover property (select ##1 !select);
  cover property (!select ##1  select);
endmodule

bind mux_functional mux_functional_sva mux_functional_chk (.*);

// -------------------- functional_module SVA --------------------
module functional_module_sva (
  input logic [1:0] in,
  input logic [1:0] out
);
  default clocking cb @(
    posedge in[0] or negedge in[0] or
    posedge in[1] or negedge in[1]
  ); endclocking

  // Bitwise inversion
  property p_inv;
    disable iff ($isunknown(in))
      out == ~in;
  endproperty
  assert property (p_inv);

  // Coverage: all input combinations
  cover property (in == 2'b00);
  cover property (in == 2'b01);
  cover property (in == 2'b10);
  cover property (in == 2'b11);
endmodule

bind functional_module functional_module_sva functional_module_chk (.*);

// -------------------- top_module SVA --------------------
module top_module_sva (
  input logic a,
  input logic b,
  input logic select,
  input logic [1:0] out
);
  default clocking cb @(
    posedge a or negedge a or
    posedge b or negedge b or
    posedge select or negedge select
  ); endclocking

  // End-to-end functional equivalence
  property p_top_compose;
    disable iff ($isunknown({a,b,select}))
      out == ~{1'b0, (select ? a : b)};
  endproperty
  assert property (p_top_compose);

  // Strong derived checks
  property p_out1_const1;
    disable iff ($isunknown({a,b,select}))
      out[1] == 1'b1;
  endproperty
  assert property (p_out1_const1);

  // Coverage: observe the four expected output patterns
  cover property (!select && (b==1'b0) && (out==2'b11));
  cover property (!select && (b==1'b1) && (out==2'b10));
  cover property ( select && (a==1'b0) && (out==2'b11));
  cover property ( select && (a==1'b1) && (out==2'b10));

  // Coverage: select toggles
  cover property (select ##1 !select);
  cover property (!select ##1  select);
endmodule

bind top_module top_module_sva top_module_chk (.*);