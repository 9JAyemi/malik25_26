// SVA for crc. Bind this onto the DUT. Focused, concise, and parameter-safe.

module crc_sva #(
  parameter int CRC_WIDTH   = 32,
  parameter int DATA_WIDTH  = 8,
  parameter      POLYNOMIAL = 32'h04C11DB7,
  parameter      SEED       = 32'hFFFFFFFF
)(
  input  logic                      clk,
  input  logic                      rst,
  input  logic [DATA_WIDTH-1:0]     data_in,
  input  logic [CRC_WIDTH-1:0]      crc_out,
  input  logic [CRC_WIDTH-1:0]      crc_reg,       // internal
  input  logic [CRC_WIDTH-1:0]      polynomial     // internal
);

  default clocking cb @(posedge clk); endclocking

  // Static parameter sanity
  initial begin
    assert (CRC_WIDTH > 0) else $error("CRC_WIDTH must be > 0");
    assert (DATA_WIDTH > 0) else $error("DATA_WIDTH must be > 0");
    assert (DATA_WIDTH <= CRC_WIDTH) else $error("DATA_WIDTH must be <= CRC_WIDTH");
  end

  // Basic well-formedness
  ap_inputs_known:  assert property (cb !$isunknown({rst, data_in}));         // no X/Z on inputs
  ap_poly_const:    assert property (cb polynomial == POLYNOMIAL);            // polynomial constant
  ap_out_is_inv:    assert property (cb crc_out == ~crc_reg);                 // combinational invert

  // Reset behavior
  ap_reset_seed:    assert property (cb rst |=> crc_reg == SEED);
  ap_reset_hold:    assert property (cb rst ##1 rst |-> $stable(crc_reg) && crc_reg == SEED);

  // Update behavior: last-NBA-wins semantics captured exactly
  // If previous MSB was 1, next crc_reg is prior crc_reg XOR polynomial (ignores shift/data_in)
  ap_msb1_update:   assert property (cb $past(!rst) && $past(crc_reg[CRC_WIDTH-1])
                                     |=> crc_reg == ($past(crc_reg) ^ $past(polynomial)));

  // If previous MSB was 0, next crc_reg is (prior << DATA_WIDTH) with low slice XOR data_in
  if (CRC_WIDTH > DATA_WIDTH) begin : g_msb0_hi
    ap_msb0_hi: assert property (cb $past(!rst) && !$past(crc_reg[CRC_WIDTH-1])
                                 |=> crc_reg[CRC_WIDTH-1:DATA_WIDTH] == $past(crc_reg[CRC_WIDTH-1-DATA_WIDTH:0]));
  end
  ap_msb0_lo: assert property (cb $past(!rst) && !$past(crc_reg[CRC_WIDTH-1])
                               |=> crc_reg[DATA_WIDTH-1:0] == ($past(crc_reg[DATA_WIDTH-1:0]) ^ $past(data_in)));

  // Output known after coming out of reset
  ap_out_known_post_reset: assert property (cb $past(!rst) |-> !$isunknown(crc_out));

  // Minimal, meaningful coverage
  cp_reset:  cover property (cb rst ##1 !rst && crc_reg == SEED);
  cp_msb1:   cover property (cb $past(!rst) && $past(crc_reg[CRC_WIDTH-1])
                             |=> crc_reg == ($past(crc_reg) ^ $past(polynomial)));
  cp_msb0:   cover property (cb $past(!rst) && !$past(crc_reg[CRC_WIDTH-1])
                             |=> 1);

endmodule

// Bind into DUT (assumes visibility of internal crc_reg and polynomial)
bind crc crc_sva #(.CRC_WIDTH(CRC_WIDTH),
                   .DATA_WIDTH(DATA_WIDTH),
                   .POLYNOMIAL(POLYNOMIAL),
                   .SEED(SEED))
u_crc_sva(.clk(clk),
          .rst(rst),
          .data_in(data_in),
          .crc_out(crc_out),
          .crc_reg(crc_reg),
          .polynomial(polynomial));