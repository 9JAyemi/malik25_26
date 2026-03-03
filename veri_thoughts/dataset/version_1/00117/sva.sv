// SVA for register_4bit
module register_4bit_sva (
  input logic        CLK,
  input logic        RST,
  input logic        LD,
  input logic [3:0]  D,
  input logic [3:0]  Q,
  input logic [3:0]  reg_Q,
  input logic [3:0]  rst_d
);

  default clocking cb @(posedge CLK); endclocking

  // Async reset clears immediately
  property p_async_reset_clears;
    @(posedge RST) ##0 (reg_Q == 4'h0 && Q == 4'h0);
  endproperty
  assert property (p_async_reset_clears);

  // Q mirrors reg_Q on clock or reset events
  assert property (@(posedge CLK or posedge RST) ##0 (Q == reg_Q));

  // While in reset, outputs remain zero on each clock
  assert property (@(posedge CLK) RST |-> (Q == 4'h0 && reg_Q == 4'h0));

  // Next-state function (covers load and hold)
  assert property (disable iff (RST)
                   1'b1 |=> (Q == ($past(LD) ? $past(D) : $past(Q))));

  // Inputs known on clock edges
  assert property (@(posedge CLK) !$isunknown({RST, LD, D}));

  // rst_d mapping correctness
  assert property (@(posedge CLK or posedge RST) ##0 (rst_d == {4{~RST}}));

  // Coverage

  // See reset assertion
  cover property (@(posedge RST) 1);

  // After reset release, see a load then a hold
  cover property (@(posedge CLK) $fell(RST) ##1 LD ##1 !LD);

  // Load that changes value
  cover property (disable iff (RST)
                  (LD && (D != $past(Q))) |=> (Q == $past(D)));

  // Hold stable for 2 cycles
  cover property (disable iff (RST)
                  (!LD)[*2] ##1 (Q == $past(Q,1) && Q == $past(Q,2)));

  // Per-bit toggle coverage on loads
  genvar i;
  generate
    for (i=0; i<4; i++) begin : gen_cov_bits
      cover property (disable iff (RST)
                      ($past(Q[i])==1'b0 && LD && D[i]==1'b1) |=> (Q[i]==1'b1));
      cover property (disable iff (RST)
                      ($past(Q[i])==1'b1 && LD && D[i]==1'b0) |=> (Q[i]==1'b0));
    end
  endgenerate

endmodule

// Bind into DUT
bind register_4bit register_4bit_sva sva (
  .CLK   (CLK),
  .RST   (RST),
  .LD    (LD),
  .D     (D),
  .Q     (Q),
  .reg_Q (reg_Q),
  .rst_d (rst_d)
);