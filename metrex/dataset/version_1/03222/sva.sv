// SVA for csr. Bind this to the DUT.
// Focus: reset values, address range safety, read mux correctness,
// write semantics (byte writes), zero-extension on rate, and concise coverage.

module csr_sva #(
  parameter int NUM_CH = 8,
  parameter int NUM_SPDIF_IN = 3,
  parameter int NUM_RATE = 5,
  parameter int VOL_WIDTH = NUM_CH*32,
  parameter int NKMDDBG_WIDTH = 16*8,
  parameter int RATE_WIDTH = NUM_SPDIF_IN*NUM_RATE,
  parameter int UDATA_WIDTH = NUM_SPDIF_IN*192,
  parameter int CDATA_WIDTH = UDATA_WIDTH
)(
  input  logic                     clk,
  input  logic                     rst,
  input  logic [11:0]              addr_i,
  input  logic                     ack_i,
  input  logic [7:0]               data_i,
  output logic [7:0]               data_o,
  output logic [(VOL_WIDTH-1):0]   vol_o,
  output logic                     nkmd_rst_o,
  input  logic [(NKMDDBG_WIDTH-1):0] nkmd_dbgout_i,
  output logic [(NKMDDBG_WIDTH-1):0] nkmd_dbgin_o,
  input  logic [(RATE_WIDTH-1):0]  rate_i,
  input  logic [(UDATA_WIDTH-1):0] udata_i,
  input  logic [(CDATA_WIDTH-1):0] cdata_i
);

  // Local decodes
  wire [3:0] addr_tag    = addr_i[11:8];
  wire [7:0] addr_offset = addr_i[7:0];

  // Derived constants
  localparam int VOL_BYTES     = VOL_WIDTH/8;
  localparam int NKMDDBG_BYTES = NKMDDBG_WIDTH/8;
  localparam int UDATA_BYTES   = UDATA_WIDTH/8;
  localparam int CDATA_BYTES   = CDATA_WIDTH/8;
  localparam int RATE_ENTRIES  = (NUM_RATE==0) ? 0 : (RATE_WIDTH/NUM_RATE);

  // Parameter sanity
  initial begin
    assert (NUM_RATE > 0 && NUM_RATE <= 8) else $error("NUM_RATE must be 1..8");
    assert (VOL_WIDTH % 8 == 0) else $error("VOL_WIDTH must be multiple of 8");
    assert (NKMDDBG_WIDTH % 8 == 0) else $error("NKMDDBG_WIDTH must be multiple of 8");
    assert (UDATA_WIDTH % 8 == 0) else $error("UDATA_WIDTH must be multiple of 8");
    assert (CDATA_WIDTH == UDATA_WIDTH) else $error("CDATA_WIDTH must equal UDATA_WIDTH");
    assert (RATE_WIDTH == NUM_SPDIF_IN*NUM_RATE) else $error("RATE_WIDTH mismatch");
  end

  // Reset defaults
  assert property (@(posedge clk)
    rst |-> (vol_o == {(NUM_CH*2){16'h00ff}} && nkmd_rst_o && nkmd_dbgin_o == '0)
  );

  // Address range safety (reads)
  assert property (@(posedge clk) (!rst && addr_tag==4'h0) |-> (addr_offset < VOL_BYTES));
  assert property (@(posedge clk) (!rst && addr_tag==4'h5) |-> (addr_offset < NKMDDBG_BYTES));
  assert property (@(posedge clk) (!rst && addr_tag==4'h6) |-> (addr_offset < NKMDDBG_BYTES));
  assert property (@(posedge clk) (!rst && addr_tag==4'h8) |-> (addr_offset < RATE_ENTRIES));
  assert property (@(posedge clk) (!rst && addr_tag==4'h9) |-> (addr_offset < UDATA_BYTES));
  assert property (@(posedge clk) (!rst && addr_tag==4'ha) |-> (addr_offset < CDATA_BYTES));

  // Address range safety (writes)
  assert property (@(posedge clk) disable iff (rst)
    ack_i && addr_tag==4'h0 |-> (addr_offset < VOL_BYTES)
  );
  assert property (@(posedge clk) disable iff (rst)
    ack_i && addr_tag==4'h6 |-> (addr_offset < NKMDDBG_BYTES)
  );

  // Read mux correctness
  assert property (@(posedge clk)
    addr_tag==4'h0 |-> data_o == vol_o[(addr_offset*8) +: 8]
  );
  assert property (@(posedge clk)
    addr_tag==4'h4 |-> (data_o[0] == nkmd_rst_o && data_o[7:1] == '0)
  );
  assert property (@(posedge clk)
    addr_tag==4'h5 |-> data_o == nkmd_dbgout_i[(addr_offset*8) +: 8]
  );
  assert property (@(posedge clk)
    addr_tag==4'h6 |-> data_o == nkmd_dbgin_o[(addr_offset*8) +: 8]
  );
  assert property (@(posedge clk)
    addr_tag==4'h8 |-> data_o[NUM_RATE-1:0] == rate_i[(addr_offset*NUM_RATE) +: NUM_RATE]
  );
  if (NUM_RATE < 8) begin
    assert property (@(posedge clk)
      addr_tag==4'h8 |-> data_o[7:NUM_RATE] == '0
    );
  end
  assert property (@(posedge clk)
    addr_tag==4'h9 |-> data_o == udata_i[(addr_offset*8) +: 8]
  );
  assert property (@(posedge clk)
    addr_tag==4'ha |-> data_o == cdata_i[(addr_offset*8) +: 8]
  );
  assert property (@(posedge clk)
    !(addr_tag inside {4'h0,4'h4,4'h5,4'h6,4'h8,4'h9,4'ha}) |-> data_o == 8'h00
  );

  // Byte-precise write semantics: vol_o
  genvar vb;
  generate
    for (vb = 0; vb < VOL_BYTES; vb++) begin : g_vol_w
      assert property (@(posedge clk) disable iff (rst)
        ack_i && addr_tag==4'h0 |-> ##1
          vol_o[(vb*8) +: 8] ==
            (vb == $past(addr_offset) ? $past(data_i) : $past(vol_o[(vb*8) +: 8]))
      );
    end
  endgenerate

  // Byte-precise write semantics: nkmd_dbgin_o
  genvar nb;
  generate
    for (nb = 0; nb < NKMDDBG_BYTES; nb++) begin : g_dbgin_w
      assert property (@(posedge clk) disable iff (rst)
        ack_i && addr_tag==4'h6 |-> ##1
          nkmd_dbgin_o[(nb*8) +: 8] ==
            (nb == $past(addr_offset) ? $past(data_i) : $past(nkmd_dbgin_o[(nb*8) +: 8]))
      );
    end
  endgenerate

  // Single-bit write semantics: nkmd_rst_o
  assert property (@(posedge clk) disable iff (rst)
    ack_i && addr_tag==4'h4 |-> ##1 nkmd_rst_o == $past(data_i[0])
  );
  assert property (@(posedge clk) disable iff (rst)
    ack_i && addr_tag!=4'h4 |-> ##1 nkmd_rst_o == $past(nkmd_rst_o)
  );

  // Optional stability when writing other tags (concise, excludes reset in next cycle)
  assert property (@(posedge clk) disable iff (rst)
    ack_i && addr_tag!=4'h0 |-> ##1 (rst || vol_o == $past(vol_o))
  );
  assert property (@(posedge clk) disable iff (rst)
    ack_i && addr_tag!=4'h6 |-> ##1 (rst || nkmd_dbgin_o == $past(nkmd_dbgin_o))
  );

  // Basic coverage
  cover property (@(posedge clk) !rst && addr_tag==4'h0);
  cover property (@(posedge clk) !rst && addr_tag==4'h4);
  cover property (@(posedge clk) !rst && addr_tag==4'h5);
  cover property (@(posedge clk) !rst && addr_tag==4'h6);
  cover property (@(posedge clk) !rst && addr_tag==4'h8);
  cover property (@(posedge clk) !rst && addr_tag==4'h9);
  cover property (@(posedge clk) !rst && addr_tag==4'ha);

  // Boundary address coverage
  cover property (@(posedge clk) !rst && addr_tag==4'h0 && addr_offset==0);
  cover property (@(posedge clk) !rst && addr_tag==4'h0 && addr_offset==VOL_BYTES-1);
  cover property (@(posedge clk) !rst && addr_tag==4'h6 && addr_offset==0);
  cover property (@(posedge clk) !rst && addr_tag==4'h6 && addr_offset==NKMDDBG_BYTES-1);
  cover property (@(posedge clk) !rst && addr_tag==4'h5 && addr_offset==NKMDDBG_BYTES-1);
  cover property (@(posedge clk) !rst && addr_tag==4'h8 && addr_offset==RATE_ENTRIES-1);
  cover property (@(posedge clk) !rst && addr_tag==4'h9 && addr_offset==0);
  cover property (@(posedge clk) !rst && addr_tag==4'ha && addr_offset==CDATA_BYTES-1);

  // Write-readback cover: vol byte
  cover property (@(posedge clk) disable iff (rst)
    ack_i && addr_tag==4'h0 ##1 (addr_tag==4'h0 && addr_offset==$past(addr_offset) &&
                                 data_o==$past(data_i))
  );

  // nkmd_rst toggle cover
  cover property (@(posedge clk) disable iff (rst)
    ack_i && addr_tag==4'h4 && data_i[0]==1'b0 ##1
    ack_i && addr_tag==4'h4 && data_i[0]==1'b1
  );

endmodule

// Bind into the DUT
bind csr csr_sva #(
  .NUM_CH(NUM_CH),
  .NUM_SPDIF_IN(NUM_SPDIF_IN),
  .NUM_RATE(NUM_RATE),
  .VOL_WIDTH(VOL_WIDTH),
  .NKMDDBG_WIDTH(NKMDDBG_WIDTH),
  .RATE_WIDTH(RATE_WIDTH),
  .UDATA_WIDTH(UDATA_WIDTH),
  .CDATA_WIDTH(CDATA_WIDTH)
) csr_sva_b (.*);