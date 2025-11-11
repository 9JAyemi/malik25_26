// SystemVerilog Assertions for top_module
// Bindable SVA focusing on reset, mux, adder, and registered timing

module top_module_sva (
  input logic        clk,
  input logic        reset,
  input logic [3:0]  in1,
  input logic [3:0]  in2,
  input logic        select,
  input logic [3:0]  add1,
  input logic [3:0]  add2,
  // internal wires
  input logic [3:0]  mux_sel,
  input logic [3:0]  add_sum,
  // registered outputs
  input logic [3:0]  mux_out,
  input logic [3:0]  add_out,
  input logic [3:0]  final_out
);

  default clocking cb @(posedge clk); endclocking

  // Combinational correctness of submodules (at sample edge)
  assert property (mux_sel == (select ? in2 : in1))
    else $error("mux_sel != mux(in1,in2,select)");
  assert property (add_sum == ((add1 + add2) & 4'hF))
    else $error("add_sum != (add1+add2)[3:0]");

  // Synchronous reset behavior
  assert property (reset |=> (mux_out==4'h0 && add_out==4'h0 && final_out==4'h0))
    else $error("Outputs not zero 1-cycle after reset asserted");
  assert property ($past(reset) && reset |-> (mux_out==4'h0 && add_out==4'h0 && final_out==4'h0))
    else $error("Outputs not held at zero while reset is held");

  // Registered timing: outputs follow previous-cycle comb values
  assert property (!reset |-> (mux_out == $past(mux_sel)))
    else $error("mux_out != $past(mux_sel)");
  assert property (!reset |-> (add_out == $past(add_sum)))
    else $error("add_out != $past(add_sum)");
  assert property (!reset |-> (final_out == $past(mux_sel ^ add_sum)))
    else $error("final_out != $past(mux_sel ^ add_sum)");

  // Internal consistency: final_out must equal mux_out ^ add_out every cycle
  assert property (final_out == (mux_out ^ add_out))
    else $error("final_out != mux_out ^ add_out");

  // X/Z propagation check: known inputs imply known internals/outputs
  assert property (!$isunknown({in1,in2,select,add1,add2}) |->
                   !$isunknown({mux_sel,add_sum,mux_out,add_out,final_out}))
    else $error("Unknown/Z propagated to outputs/internal wires");

  // Coverage
  cover property (reset ##1 !reset);                                  // reset pulse
  cover property (!reset && (in1!=in2) && (select==0) ##1 mux_out==$past(in1)); // mux selects in1
  cover property (!reset && (in1!=in2) && (select==1) ##1 mux_out==$past(in2)); // mux selects in2
  cover property (!reset && ((add1 + add2) > 4'hF));                  // adder overflow/wrap
  cover property (!reset && (mux_out ^ add_out) == 4'h0);             // XOR all-zero
  cover property (!reset && (mux_out ^ add_out) == 4'hF);             // XOR all-ones
  cover property (!reset && $changed(select));                        // select toggles

endmodule

bind top_module top_module_sva sva_i (
  .clk(clk),
  .reset(reset),
  .in1(in1),
  .in2(in2),
  .select(select),
  .add1(add1),
  .add2(add2),
  .mux_sel(mux_sel),
  .add_sum(add_sum),
  .mux_out(mux_out),
  .add_out(add_out),
  .final_out(final_out)
);