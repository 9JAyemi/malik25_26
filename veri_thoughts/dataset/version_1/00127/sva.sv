// SVA for top_module, four_bit_adder, barrel_shifter
// Clockless concurrent assertions using @(*). Bind as shown below.

module top_module_sva (
  input  [3:0] DIN,
  input  [1:0] SHIFT,
  input  [3:0] a,
  input  [3:0] b,
  input        cin,
  input        cout,
  input  [3:0] sum,
  input  [3:0] DOUT
);
  // Golden model
  let shifted_g = {DIN[SHIFT[1]], DIN[SHIFT[0]], DIN[3], DIN[2]};
  let add5_g    = ({1'b0,a} + {1'b0,shifted_g} + cin);
  let adder_sum_g  = add5_g[3:0];
  let adder_cout_g = add5_g[4];
  let sum5_g    = ({1'b0,adder_sum_g} + {1'b0,b} + cin);
  let sum_g     = sum5_g[3:0];

  // Functional correctness
  assert property (@(*) DOUT == adder_sum_g);
  assert property (@(*) cout == adder_cout_g);
  assert property (@(*) sum  == sum_g);

  // X-prop: if inputs known, outputs known
  assert property (@(*) (!$isunknown({DIN,SHIFT,a,b,cin})) |-> !$isunknown({cout,sum,DOUT}));

  // Coverage
  cover property (@(*) SHIFT==2'b00);
  cover property (@(*) SHIFT==2'b01);
  cover property (@(*) SHIFT==2'b10);
  cover property (@(*) SHIFT==2'b11);
  cover property (@(*) cin==1'b0);
  cover property (@(*) cin==1'b1);
  cover property (@(*) adder_cout_g==1'b1);   // first add carry out
  cover property (@(*) sum5_g[4]==1'b1);      // second add overflow
  cover property (@(*) DOUT==4'h0);
  cover property (@(*) DOUT==4'hF);
endmodule


module four_bit_adder_sva (
  input  [3:0] a,
  input  [3:0] b,
  input        cin,
  input        cout,
  input  [3:0] sum
);
  let add5 = ({1'b0,a} + {1'b0,b} + cin);

  // Functional correctness
  assert property (@(*) {cout,sum} == add5);

  // X-prop
  assert property (@(*) (!$isunknown({a,b,cin})) |-> !$isunknown({cout,sum}));

  // Coverage
  cover property (@(*) cin==1'b0);
  cover property (@(*) cin==1'b1);
  cover property (@(*) add5[4]==1'b1);  // carry out
  cover property (@(*) sum==4'h0);
  cover property (@(*) sum==4'hF);
endmodule


module barrel_shifter_sva (
  input  [3:0] DIN,
  input  [1:0] SHIFT,
  input  [3:0] DOUT
);
  // Functional correctness (as implemented)
  assert property (@(*) DOUT == {DIN[SHIFT[1]], DIN[SHIFT[0]], DIN[3], DIN[2]});

  // X-prop
  assert property (@(*) (!$isunknown({DIN,SHIFT})) |-> !$isunknown(DOUT));

  // Coverage
  cover property (@(*) SHIFT==2'b00);
  cover property (@(*) SHIFT==2'b01);
  cover property (@(*) SHIFT==2'b10);
  cover property (@(*) SHIFT==2'b11);
endmodule


// Bind these in your testbench/top-level scope (adjust instance paths if needed):
// bind top_module      top_module_sva      u_top_sva      (.*);
// bind four_bit_adder  four_bit_adder_sva  u_adder_sva    (.*);
// bind barrel_shifter  barrel_shifter_sva  u_shifter_sva  (.*);