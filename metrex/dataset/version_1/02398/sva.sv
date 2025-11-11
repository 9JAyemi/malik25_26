// SVA checker for shift_register
module shift_register_sva (
  input logic        clk,
  input logic        d,
  input logic        q,
  input logic [2:0]  reg_q
);
  default clocking cb @(posedge clk); endclocking

  // Bookkeeping for safe $past usage and known-input window
  bit         past1;
  logic [1:0] age;
  logic [2:0] d_known; // shift of "d is known" over last 3 cycles

  initial begin
    past1   = 1'b0;
    age     = 2'd0;
    d_known = 3'b000;
  end

  always_ff @(posedge clk) begin
    past1   <= 1'b1;
    if (age != 2'd3) age <= age + 2'd1;
    d_known <= {d_known[1:0], ! $isunknown(d)};
  end

  wire past3 = (age == 2'd3);

  // A1: One-cycle next-state check of the shift behavior (when drivers are known)
  assert property (
    past1 && !$isunknown({$past(reg_q[1:0]), $past(d)}) |-> reg_q == {$past(reg_q[1:0]), $past(d)}
  );

  // A2: Output must be alias of MSB
  assert property ( q === reg_q[2] );

  // A3: After 3 cycles of known inputs, q is the 3-cycle delayed d and is known
  assert property (
    past3 && (&d_known) |-> ( q === $past(d,3) && !$isunknown(q) )
  );

  // Coverage: observe both q values, both edges, and extreme internal states
  cover property ( past3 && (&d_known) && q == 1'b0 );
  cover property ( past3 && (&d_known) && q == 1'b1 );
  cover property ( past3 && $rose(q) );
  cover property ( past3 && $fell(q) );
  cover property ( reg_q == 3'b000 );
  cover property ( reg_q == 3'b111 );
endmodule

// Bind into the DUT
bind shift_register shift_register_sva u_shift_register_sva(
  .clk(clk),
  .d(d),
  .q(q),
  .reg_q(reg_q)
);