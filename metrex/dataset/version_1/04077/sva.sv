// SVA for signal_modifier
// Bindable checker that fully specifies functional intent and key corner cases.
// Provide any convenient clock from your environment when binding.

checker signal_modifier_sva(
  input logic        clk,
  input logic [15:0] in,
  input logic [1:0]  ctrl,
  input logic [15:0] out
);
  default clocking cb @(posedge clk); endclocking

  function automatic logic [15:0] spec_out(logic [15:0] i, logic [1:0] c);
    case (c)
      2'b00: spec_out = i;
      2'b01: spec_out = ~i;
      2'b10: spec_out = {i[13:0], 2'b00};
      2'b11: spec_out = {2'b00, i[15:2]};
      default: spec_out = 'x;
    endcase
  endfunction

  // Core functional equivalence (guards out X/Z on inputs)
  a_functional: assert property ( !$isunknown({in,ctrl}) |-> out == spec_out(in, ctrl) );

  // Targeted checks for each mode (help localize failures)
  a_pass:  assert property ( (ctrl==2'b00) |-> out == in );
  a_not:   assert property ( (ctrl==2'b01) |-> (out ^ in) == 16'hFFFF );
  a_sll2:  assert property ( (ctrl==2'b10) |-> (out[1:0]==2'b00 && out[15:2]==in[13:0]) );
  a_srl2:  assert property ( (ctrl==2'b11) |-> (out[15:14]==2'b00 && out[13:0]==in[15:2]) );

  // Out has no X/Z when inputs are known
  a_no_x_when_known: assert property ( !$isunknown({in,ctrl}) |-> !$isunknown(out) );

  // Coverage: exercise all modes and nontrivial patterns
  c_mode_00: cover property (ctrl==2'b00);
  c_mode_01: cover property (ctrl==2'b01);
  c_mode_10: cover property (ctrl==2'b10);
  c_mode_11: cover property (ctrl==2'b11);

  c_sll2_activity: cover property (ctrl==2'b10 && in[13:0]!=16'h0);
  c_srl2_activity: cover property (ctrl==2'b11 && in[15:2]!=14'h0);
  c_not_mixed:     cover property (ctrl==2'b01 && in!=16'h0000 && in!=16'hFFFF);

  // Optional: basic mode transitions to ensure all case arms toggle in sim
  c_switch_00_01: cover property ( (ctrl==2'b00) ##1 (ctrl==2'b01) );
  c_switch_01_10: cover property ( (ctrl==2'b01) ##1 (ctrl==2'b10) );
  c_switch_10_11: cover property ( (ctrl==2'b10) ##1 (ctrl==2'b11) );
  c_switch_11_00: cover property ( (ctrl==2'b11) ##1 (ctrl==2'b00) );
endchecker

// Example bind (replace tb_clk with your clock):
// bind signal_modifier signal_modifier_sva u_sva(.clk(tb_clk), .in(in), .ctrl(ctrl), .out(out));