// SVA for fifo: bindable, concise, full functional checks and coverage

module fifo_sva (
  input  logic        clk,
  input  logic        wr0a, wr0b, wr1a, wr1b,
  input  logic [15:0] inData,
  input  logic [15:0] out0, out1,
  input  logic [15:0] mem0, mem1
);

  // guard for $past()
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Next-state function (including precedence: b overrides a)
  property p_mem0_next;
    @(posedge clk) disable iff (!past_valid)
      1'b1 |=> mem0 == $past( wr0b ? ~inData :
                              wr0a ?  inData :
                                       mem0 );
  endproperty
  assert property (p_mem0_next);

  property p_mem1_next;
    @(posedge clk) disable iff (!past_valid)
      1'b1 |=> mem1 == $past( wr1b ? ~inData :
                              wr1a ?  inData :
                                       mem1 );
  endproperty
  assert property (p_mem1_next);

  // Outputs mirror storage
  assert property (@(posedge clk) out0 == mem0);
  assert property (@(posedge clk) out1 == mem1);

  // X/z hygiene
  assert property (@(posedge clk) disable iff (!past_valid) !$isunknown({wr0a, wr0b, wr1a, wr1b}));
  assert property (@(posedge clk) disable iff (!past_valid) (wr0a || wr0b || wr1a || wr1b) |-> !$isunknown(inData));

  // Coverage: all write modes per entry + concurrent writes + precedence
  cover property (@(posedge clk) wr0a && !wr0b);
  cover property (@(posedge clk) wr0b);                 // includes wr0b-only and both-high
  cover property (@(posedge clk) !wr0a && !wr0b);
  cover property (@(posedge clk) wr1a && !wr1b);
  cover property (@(posedge clk) wr1b);                 // includes wr1b-only and both-high
  cover property (@(posedge clk) !wr1a && !wr1b);
  cover property (@(posedge clk) (wr0a || wr0b) && (wr1a || wr1b));
  cover property (@(posedge clk) wr0a && wr0b |=> mem0 == $past(~inData));
  cover property (@(posedge clk) wr1a && wr1b |=> mem1 == $past(~inData));

endmodule

bind fifo fifo_sva u_fifo_sva (
  .clk(clk),
  .wr0a(wr0a), .wr0b(wr0b),
  .wr1a(wr1a), .wr1b(wr1b),
  .inData(inData),
  .out0(out0), .out1(out1),
  .mem0(mem[0]), .mem1(mem[1])
);