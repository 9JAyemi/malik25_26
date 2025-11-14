// SystemVerilog Assertions for bcd_counter
// Bindable SVA module (references internal regs)
module bcd_counter_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [3:0]  count,
  input  logic [3:0]  bcd_count,
  input  logic [2:0]  ena,
  input  logic [15:0] q
);

  // start flag to safely use $past
  logic started;
  always_ff @(posedge clk or posedge reset)
    if (reset) started <= 1'b0; else started <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  // Async reset effect (sampled at clk): state is 0 while reset is 1
  assert property (reset |-> (count==4'd0 && bcd_count==4'd0));

  // No X/Z after reset releases
  assert property (disable iff (reset || !started) !$isunknown({ena,q,count,bcd_count}));

  // IMPLEMENTATION-LEVEL TRANSITION CHECKS (match RTL semantics)
  assert property (disable iff (reset || !started) ($past(count) <= 4'd8)  |-> count == $past(count)+1);
  assert property (disable iff (reset || !started) ($past(count) == 4'd9) |-> count == 4'd10);
  assert property (disable iff (reset || !started) ($past(count) == 4'd10)|-> count == 4'd0);

  // bcd_count updates only on wrap (when previous count was 10)
  assert property (disable iff (reset || !started) ($past(count)==4'd10)  |-> bcd_count == $past(bcd_count)+1);
  assert property (disable iff (reset || !started) ($past(count)!=4'd10)  |-> $stable(bcd_count));

  // SPEC-LEVEL CHECK: count must stay in BCD range 0..9 (flags the design bug)
  assert property (disable iff (reset) count <= 4'd9)
    else $error("Count went out of BCD range (0..9)");

  // Output relationships
  // q shows {count,bcd_count} in low byte when count in 0..9; otherwise 0
  assert property (disable iff (reset) (count <= 4'd9) |-> q == {count,bcd_count});
  assert property (disable iff (reset) (count >  4'd9) |-> q == 16'h0000);
  // ena mirrors low 3 bits of bcd_count
  assert property (ena == bcd_count[2:0]);

  // Coverage
  cover property (disable iff (reset) (count==4'd9 ##1 count==4'd10 ##1 count==4'd0)); // wrap
  cover property (disable iff (reset) (count==4'd10));                                  // default case hit
  cover property (disable iff (reset || !started) ($past(count)==4'd10 && bcd_count==$past(bcd_count)+1)); // bcd inc
  cover property (disable iff (reset) $changed(ena));

endmodule

// Bind into DUT (accesses internals by name)
bind bcd_counter bcd_counter_sva sva_i (.clk(clk),
                                        .reset(reset),
                                        .count(count),
                                        .bcd_count(bcd_count),
                                        .ena(ena),
                                        .q(q));