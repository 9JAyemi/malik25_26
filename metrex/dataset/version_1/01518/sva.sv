// SVA for original_gate: concise, full functional check + coverage
module original_gate_sva (
  input  logic        clk,
  input  logic [4:0]  ctrl,
  input  logic [1:0]  din,
  input  logic        sel,
  input  logic [31:0] dout
);

  // Track we've got a valid $past() sample
  logic started;
  always_ff @(posedge clk) started <= 1'b1;

  // Effective case index: ctrl*sel == (sel ? ctrl : 0)
  logic [5:0] idx;
  assign idx = sel ? {1'b0,ctrl} : 6'd0;

  // Sanity: inputs must be known at the sampling edge
  assert property (@(posedge clk) !$isunknown({sel,ctrl,din}));

  // Sanity: output should be known after update
  assert property (@(posedge clk) started |-> !$isunknown(dout));

  // Core functional equivalence (covers all ctrl*sel in [0..31])
  // dout_next == lower_bits_preserved | (zero-extended din placed at idx), upper bits zeroed
  property p_functional;
    @(posedge clk)
      started |->
        dout ==
          ( ($past(dout) & ((32'h1 << $past(idx)) - 32'h1)) |
            ( ({30'b0,$past(din)}) << $past(idx) ) );
  endproperty
  assert property (p_functional);

  // Explicit check for the case idx==0 (sel==0 or ctrl==0)
  assert property (@(posedge clk) started && ($past(idx)==0)
                   |-> dout == {30'b0,$past(din)});

  // Functional coverage: hit every case item 0..31
  genvar i;
  generate
    for (i=0; i<32; i++) begin : C_IDX
      cover property (@(posedge clk) started && ($past(idx)==i));
    end
  endgenerate

  // Coverage: exercise both sel values
  cover property (@(posedge clk) started && $past(sel)==0);
  cover property (@(posedge clk) started && $past(sel)==1);

endmodule

// Bind into DUT
bind original_gate original_gate_sva sva_inst (
  .clk  (clk),
  .ctrl (ctrl),
  .din  (din),
  .sel  (sel),
  .dout (dout)
);