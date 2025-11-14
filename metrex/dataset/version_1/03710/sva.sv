// SVA for byte_en_reg
// Bind or instantiate alongside the DUT. Focused, parameterized, and byte-accurate.

module byte_en_reg_sva #(
  parameter int DATA_W   = 32,
  parameter      INIT_VAL = {DATA_W{1'b0}}
) (
  input  logic                   clk,
  input  logic                   rst,
  input  logic                   we,
  input  logic [(DATA_W-1)/8:0]  en,
  input  logic [DATA_W-1:0]      d,
  input  logic [DATA_W-1:0]      q
);

  localparam int BYTES = (DATA_W+7)/8;

  // Basic structural sanity
  initial begin
    assert ($bits(en) == BYTES) else $error("en width mismatch");
    assert ($bits(q)  == DATA_W);
    assert ($bits(d)  == DATA_W);
  end

  default clocking cb @(posedge clk); endclocking

  // X-checks on controls/data when they matter
  assert property ( !$isunknown(rst) );
  assert property ( disable iff (rst) !$isunknown(we) );
  assert property ( disable iff (rst) we |-> !$isunknown(en) );
  // Per-byte data X-checks when that byte is written (below, inside generate)

  // Asynchronous reset takes effect immediately on rst posedge
  assert property (@(posedge rst) ##0 (q == INIT_VAL));

  // While rst is high at a clk edge, q is INIT_VAL
  assert property ( rst |-> (q == INIT_VAL) );

  // No write => hold entire register
  assert property ( disable iff (rst) (!we) |=> (q == $past(q)) );

  // Write with no enables => hold entire register
  assert property ( disable iff (rst) (we && (en == '0)) |=> (q == $past(q)) );

  // Byte-accurate update/hold checks
  genvar b;
  for (b = 0; b < BYTES; b++) begin : G_BYTE
    localparam int LO = 8*b;
    localparam int HI = (8*b+7 < DATA_W) ? (8*b+7) : (DATA_W-1);

    // If this byte is enabled on a write, it must update from d
    assert property ( disable iff (rst)
      (we && en[b]) |=> (q[HI:LO] == $past(d[HI:LO]))
    );

    // If this byte is not enabled on a write, it must hold
    assert property ( disable iff (rst)
      (we && !en[b]) |=> (q[HI:LO] == $past(q[HI:LO]))
    );

    // Data driving an enabled byte must be known
    assert property ( disable iff (rst)
      (we && en[b]) |-> !$isunknown(d[HI:LO])
    );

    // Coverage: see each byte written at least once
    cover property ( disable iff (rst) (we && en[b]) );
  end

  // Coverage: global scenarios
  cover property (@(posedge rst) 1);                         // reset observed
  cover property ( disable iff (rst) (we && (en == '1)));    // multi-byte/all-byte write

endmodule

// Example bind (uncomment and adjust instance path):
// bind byte_en_reg byte_en_reg_sva #(.DATA_W(DATA_W), .INIT_VAL(INIT_VAL))
// (.*);