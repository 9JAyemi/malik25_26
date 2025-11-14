// Bindable SVA for module adder
module adder_sva (
  input  logic [7:0] data1,
  input  logic [7:0] data2,
  input  logic [7:0] out,
  input  logic [7:0] carry
);

  default clocking cb @(data1 or data2 or out or carry); endclocking
  default disable iff ($isunknown({data1, data2}));

  let sum9 = ({1'b0, data1} + {1'b0, data2});

  // Core functional checks (intended behavior, catches width/overflow bugs)
  assert property (##0 out == (sum9[7:0] + sum9[8]))
    else $error("out mismatch: expected low+carry");
  assert property (##0 carry inside {8'h00, 8'h01})
    else $error("carry not 0/1");
  assert property (##0 carry[0] == sum9[8])
    else $error("carry bit does not reflect overflow");
  assert property (##0 carry[7:1] == '0)
    else $error("upper carry bits not zeroed");

  // Sanity: outputs known when inputs known
  assert property (##0 !$isunknown({out, carry}))
    else $error("X/Z on outputs with known inputs");

  // Sanity: output changes only if inputs changed
  assert property ($changed(out) |-> ($changed(data1) || $changed(data2)))
    else $error("out changed without input change");
  assert property ($changed(carry) |-> ($changed(data1) || $changed(data2)))
    else $error("carry changed without input change");

  // Coverage: overflow/no-overflow and key corners
  cover property (##0 sum9[8] == 1'b0);       // no overflow
  cover property (##0 sum9[8] == 1'b1);       // overflow
  cover property (##0 data1==8'h00 && data2==8'h00 && out==8'h00 && carry==8'h00);
  cover property (##0 data1==8'hFF && data2==8'h00 && out==8'hFF && carry==8'h00);
  cover property (##0 data1==8'hFF && data2==8'h01 && out==8'h01 && carry==8'h01);
  cover property (##0 data1==8'h80 && data2==8'h80 && out==8'h01 && carry==8'h01);
  cover property (##0 data1==8'hFF && data2==8'hFF && out==8'hFF && carry==8'h01);

endmodule

// Bind into DUT (hierarchical connect to internal 'carry')
bind adder adder_sva sva_adder (.data1(data1), .data2(data2), .out(out), .carry(carry));