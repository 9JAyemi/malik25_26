// SVA bind file for digital_potentiometer
// Concise, high-quality checks and coverage

module digital_pot_sva #(
  parameter int unsigned rmax         = 10000,
  parameter int unsigned rstep        = 1000,
  parameter int unsigned initial_pos  = 0
)(
  input  logic                 clk,
  input  logic [2:0]           addr,
  input  logic [6:0]           data,
  input  logic [7:0]           vout,
  input  logic [6:0]           resistances [0:7]
);

  // Param sanity
  initial begin
    assert (rmax > 0) else $error("rmax must be > 0");
    assert (initial_pos < 8) else $error("initial_pos out of range");
  end

  // Check initial contents per spec (note: truncation to 7 bits)
  initial begin : INIT_CHECK
    automatic logic [6:0] init_val = (rstep*initial_pos) & 7'h7F;
    foreach (resistances[j]) begin
      logic [6:0] exp = (j == initial_pos) ? init_val : 7'h00;
      assert (resistances[j] === exp)
        else $error("Init mismatch: resistances[%0d]=%0h exp=%0h", j, resistances[j], exp);
    end
  end

  // Clock/past_valid
  default clocking cb @(posedge clk); endclocking
  bit past_valid; initial past_valid = 0; always_ff @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Basic X checks
  assert property (!$isunknown({addr, data}))) else $error("X/Z on addr/data");
  assert property (!$isunknown(vout))) else $error("X/Z on vout");

  // Array element invariants: 7-bit range, no X
  generate
    genvar j;
    for (j=0; j<8; j++) begin : G_INV
      assert property (!$isunknown(resistances[j]))) else
        $error("X/Z on resistances[%0d]", j);
      assert property (resistances[j] inside {[7'd0:7'd127]})) else
        $error("resistances[%0d] out of range: %0d", j, resistances[j]);
    end
  endgenerate

  // Precise write/update model for the memory array
  // Each cycle, only the previously addressed entry updates to previous data; others hold.
  generate
    for (j=0; j<8; j++) begin : G_WRITE_MODEL
      assert property (
        resistances[j] ==
          ( ($past(addr) == j) ? $past(data) : $past(resistances[j]) )
      ) else $error("Array update mismatch at idx %0d", j);
    end
  endgenerate

  // vout functional correctness (uses current addr, past array contents)
  assert property (
    vout == ( ( $past(resistances[addr]) * 8'd255 ) / rmax )
  ) else $error("vout functional mismatch");

  // Latency from write to visible vout when addr held constant (2-cycle latency)
  // If addr stays the same for 3 cycles, vout on the 3rd equals data written 2 cycles earlier.
  assert property (
    (addr == $past(addr) && addr == $past(addr,2)) |->
    vout == ( ($past(data,2) * 8'd255) / rmax )
  ) else $error("Pipeline latency/write-to-vout mismatch");

  // Coverage: exercise each address with the write->read pipeline
  generate
    for (j=0; j<8; j++) begin : G_COV
      cover property (
        past_valid && addr==j ##1 addr==j ##1 (addr==j && vout == (($past(data,2)*8'd255)/rmax))
      );
    end
  endgenerate

  // Coverage: extremes
  cover property (data==7'h00 ##2 vout==8'h00);
  cover property (data==7'h7F ##2 vout == (($past(7'h7F,2)*8'd255)/rmax));

endmodule

// Bind into DUT (access internal array)
bind digital_potentiometer
  digital_pot_sva #(.rmax(rmax), .rstep(rstep), .initial_pos(initial_pos)))
    pot_sva ( .clk(clk), .addr(addr), .data(data), .vout(vout), .resistances(resistances) );