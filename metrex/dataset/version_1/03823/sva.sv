// SVA for custom_module
// Bindable, concise, full functional checks + key coverage

module custom_module_sva (
  input  logic clk,
  input  logic rst_n,

  // DUT ports
  input  logic A1, A2, B1, B2, C1,
  input  logic Y,

  // DUT internals (bound by name)
  input  logic and0_out,
  input  logic and1_out,
  input  logic nor0_out_Y
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Functional correctness (internal structure and end-to-end)
  assert property (and0_out   === (B1 & B2));
  assert property (and1_out   === (A1 & A2));
  assert property (nor0_out_Y === ~(and0_out | and1_out | C1));
  assert property (Y          === nor0_out_Y);
  assert property (Y          === ~((A1 & A2) | (B1 & B2) | C1)); // end-to-end

  // No-X propagation: if inputs known, output known
  assert property (!$isunknown({A1,A2,B1,B2,C1}) |-> !$isunknown(Y));

  // Combinational stability: if inputs didn’t change, Y shouldn’t change
  assert property (!$changed({A1,A2,B1,B2,C1}) |-> $stable(Y));

  // Coverage: key scenarios and output toggles
  cover property (~(A1 & A2) && ~(B1 & B2) && !C1 && (Y==1));                // all-low -> Y=1
  cover property ((B1 & B2) && !(A1 & A2) && !C1 && (Y==0));                // only and0 term high
  cover property ((A1 & A2) && !(B1 & B2) && !C1 && (Y==0));                // only and1 term high
  cover property (C1 && !(A1 & A2) && !(B1 & B2) && (Y==0));                // only C1 high
  cover property (((and0_out && and1_out) || (and0_out && C1) || (and1_out && C1)) && (Y==0)); // 2+ terms high
  cover property (Y ##1 !Y);                                                // Y 1->0
  cover property (!Y ##1 Y);                                                // Y 0->1
endmodule

// Example bind (place in a package or a testbench file)
// Replace tb_clk/tb_rst_n with your environment clock/reset.
bind custom_module custom_module_sva u_custom_module_sva (
  .clk(tb_clk),
  .rst_n(tb_rst_n),
  .A1(A1), .A2(A2), .B1(B1), .B2(B2), .C1(C1),
  .Y(Y),
  .and0_out(and0_out),
  .and1_out(and1_out),
  .nor0_out_Y(nor0_out_Y)
);