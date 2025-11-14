// SVA for concat
module concat_sva_bind (
  input logic        clk,
  input logic [7:0]  In0,
  input logic [1:0]  In1,
  input logic [9:0]  dout
);
  default clocking @(posedge clk); endclocking

  // Functional correctness: dout is the registered concatenation of inputs
  assert property ($past(1'b1) |-> dout == $past({In1,In0}));

  // Bit-slice mapping checks
  assert property ($past(1'b1) |-> dout[9:8] == $past(In1));
  assert property ($past(1'b1) |-> dout[7:0] == $past(In0));

  // No X/Z on output when inputs were known at sampling edge
  assert property ($past(!$isunknown({In1,In0})) |-> !$isunknown(dout));

  // No glitches between clock edges (dout only updates on posedge)
  assert property (@(negedge clk) $stable(dout));

  // Coverage
  cover property ($past(1'b1) && (dout == $past({In1,In0})));
  cover property ($past(1'b1) && $past(In1)==2'b00 && dout[9:8]==2'b00);
  cover property ($past(1'b1) && $past(In1)==2'b01 && dout[9:8]==2'b01);
  cover property ($past(1'b1) && $past(In1)==2'b10 && dout[9:8]==2'b10);
  cover property ($past(1'b1) && $past(In1)==2'b11 && dout[9:8]==2'b11);
  cover property ($past(1'b1) && $past(In0)==8'h00 && dout[7:0]==8'h00);
  cover property ($past(1'b1) && $past(In0)==8'hFF && dout[7:0]==8'hFF);
endmodule

bind concat concat_sva_bind sva_concat (.*);