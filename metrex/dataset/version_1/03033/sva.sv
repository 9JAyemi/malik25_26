// SVA for top_module and submodules (concise, quality-focused)
// Bind into DUT; no TB code required.

module top_module_sva #(parameter W=4) (
  input clk,
  input up_down,
  input [W-1:0] load,
  input SUB,
  input [W-1:0] Q,
  input [W-1:0] counter_out,
  input [W-1:0] add_sub_out
);
  default clocking cb @(posedge clk); endclocking

  // Top-level sequential select logic
  property p_top_select;
    Q == ( $past(|load) ? $past(load)
        : $past(SUB)     ? $past(add_sub_out)
                         : $past(counter_out));
  endproperty
  assert property (p_top_select);

  // Load has priority over SUB/counter paths
  assert property ( $past(|load) |-> (Q == $past(load)) );

  // Adder/subtractor functional check (combinational)
  assert property ( add_sub_out == (SUB ? (counter_out - load) : (counter_out + load)) );

  // When load==0, adder output must match counter_out (B=0)
  assert property ( !$past(|load) |-> ($past(add_sub_out) == $past(counter_out)) );

  // Coverage: exercise all output paths and priority
  cover property ( $past(|load) && (Q == $past(load)) );
  cover property ( !$past(|load) && $past(SUB)  && (Q == $past(add_sub_out)) );
  cover property ( !$past(|load) && !$past(SUB) && (Q == $past(counter_out)) );
  cover property ( $past(|load) && $past(SUB) && (Q == $past(load)) ); // load overrides SUB
endmodule


module up_down_counter_sva #(parameter W=4) (
  input clk,
  input up_down,
  input [W-1:0] load,
  input [W-1:0] Q
);
  default clocking cb @(posedge clk); endclocking

  // Counter next-state function with synchronous load (|load) as enable
  assert property (
    Q == ( $past(|load) ? $past(load)
        : $past(up_down) ? ($past(Q) + W'd1)
                         : ($past(Q) - W'd1) )
  );

  // Coverage: inc, dec, load, and wrap-around both directions
  cover property ( !$past(|load) &&  $past(up_down) && (Q == ($past(Q) + W'd1)) );
  cover property ( !$past(|load) && !$past(up_down) && (Q == ($past(Q) - W'd1)) );
  cover property (  $past(|load) && (Q == $past(load)) );
  cover property ( !$past(|load) &&  $past(up_down) && ($past(Q) == {W{1'b1}}) && (Q == {W{1'b0}}) ); // 15->0
  cover property ( !$past(|load) && !$past(up_down) && ($past(Q) == {W{1'b0}}) && (Q == {W{1'b1}}) ); // 0->15
endmodule


// Bind assertions to DUT
bind top_module       top_module_sva       #(.W(4)) i_top_sva (.*);
bind up_down_counter  up_down_counter_sva  #(.W(4)) i_udc_sva (.*);