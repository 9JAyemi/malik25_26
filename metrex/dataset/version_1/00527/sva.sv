// SVA for counter: check step behavior, period, and cover full cycle
module counter_sva(input logic clk, input logic [3:0] out);
  default clocking cb @(posedge clk); endclocking

  // Every cycle: increment by 1; wrap 15->0
  property p_step;
    !$isunknown($past(out)) |-> out == (($past(out)==4'hF) ? 4'h0 : $past(out)+4'h1);
  endproperty
  assert property (p_step);

  // 16-cycle periodicity
  property p_period16;
    !$isunknown($past(out,16)) |-> out == $past(out,16);
  endproperty
  assert property (p_period16);

  // Functional coverage: observe a full 0..15..0 cycle
  cover property (
      (out==4'h0)
   ##1 (out==4'h1)
   ##1 (out==4'h2)
   ##1 (out==4'h3)
   ##1 (out==4'h4)
   ##1 (out==4'h5)
   ##1 (out==4'h6)
   ##1 (out==4'h7)
   ##1 (out==4'h8)
   ##1 (out==4'h9)
   ##1 (out==4'hA)
   ##1 (out==4'hB)
   ##1 (out==4'hC)
   ##1 (out==4'hD)
   ##1 (out==4'hE)
   ##1 (out==4'hF)
   ##1 (out==4'h0)
  );
endmodule

bind counter counter_sva u_counter_sva (.clk(clk), .out(out));