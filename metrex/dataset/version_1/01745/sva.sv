// SVA for LogicCell
module LogicCell_sva(
  input  logic        clk,
  input  logic        clkb,
  input  logic        sr,
  input  logic        in0,
  input  logic        in1,
  input  logic        in2,
  input  logic        in3,
  input  logic        carryin,
  input  logic        lcout,
  input  logic        carryout,
  input  logic [3:0]  inputs,        // internal reg from DUT
  input  logic        lcout_reg,     // internal reg from DUT
  input  logic        carryout_reg   // internal reg from DUT
);

  // Track that at least one compute cycle has occurred since last reset
  logic started;
  always @(posedge clk or negedge clkb) begin
    if (!clkb)        started <= 1'b0;
    else if (sr)      started <= 1'b0;
    else              started <= 1'b1;
  end

  // Combinational output mapping must always hold
  assert property (@(posedge clk or negedge clkb)
    (lcout === lcout_reg) && (carryout === (carryin & carryout_reg))
  );

  // Asynchronous reset on negedge clkb
  assert property (@(negedge clkb) ##0 (lcout_reg==1'b0 && carryout_reg==1'b0));

  // Asynchronous reset effect when clkb is low on a posedge clk
  assert property (@(posedge clk) (!clkb) |-> ##0 (lcout_reg==1'b0 && carryout_reg==1'b0));

  // Synchronous reset on sr at posedge clk (when clkb is high)
  assert property (@(posedge clk) (clkb && sr) |-> ##0 (lcout_reg==1'b0 && carryout_reg==1'b0));

  // Functional update on compute cycles (after at least one non-reset compute cycle)
  // - inputs captures current in[3:0]
  // - lcout_reg is OR of previous inputs
  // - carryout_reg is AND of previous inputs
  assert property (@(posedge clk)
    (clkb && !sr && started) |-> ##0 (
      inputs == {in3,in2,in1,in0} &&
      lcout_reg == $past(|inputs) &&
      carryout_reg == $past(&inputs)
    )
  );

  // Carry-out gating behavior (redundant with mapping but explicit)
  assert property (@(posedge clk) (!carryin) |-> (carryout==1'b0));
  assert property (@(posedge clk) ( carryin) |-> (carryout===carryout_reg));

  // ------------ Coverage ------------

  // Cover async reset occurrence
  cover property (@(negedge clkb) ##0 (lcout_reg==0 && carryout_reg==0));

  // Cover synchronous reset occurrence
  cover property (@(posedge clk) (clkb && sr) ##0 (lcout_reg==0 && carryout_reg==0));

  // Cover compute cycles with representative input patterns
  cover property (@(posedge clk) (clkb && !sr) ##0 (inputs==4'b0000));
  cover property (@(posedge clk) (clkb && !sr) ##0 (inputs==4'b1111));
  cover property (@(posedge clk) (clkb && !sr) ##0 (inputs==4'b0101));

  // Cover carryin gating seen both ways
  cover property (@(posedge clk) carryin==1'b0 && clkb && !sr);
  cover property (@(posedge clk) carryin==1'b1 && clkb && !sr);

endmodule

// Bind into DUT (accesses internal regs via port connections)
bind LogicCell LogicCell_sva sva_inst (
  .clk(clk),
  .clkb(clkb),
  .sr(sr),
  .in0(in0),
  .in1(in1),
  .in2(in2),
  .in3(in3),
  .carryin(carryin),
  .lcout(lcout),
  .carryout(carryout),
  .inputs(inputs),
  .lcout_reg(lcout_reg),
  .carryout_reg(carryout_reg)
);