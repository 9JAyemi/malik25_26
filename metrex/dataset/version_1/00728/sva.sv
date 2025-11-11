// SVA for ad_mem: dual-clock write/read RAM
// Bindable, concise, and checks key behaviors

module ad_mem_sva #(
  parameter DATA_WIDTH = 16,
  parameter ADDRESS_WIDTH = 5
)(
  input  logic                    clka,
  input  logic                    wea,
  input  logic [ADDRESS_WIDTH-1:0] addra,
  input  logic [DATA_WIDTH-1:0]    dina,

  input  logic                    clkb,
  input  logic [ADDRESS_WIDTH-1:0] addrb,
  input  logic [DATA_WIDTH-1:0]    doutb,

  // observe internal RAM array
  input  logic [DATA_WIDTH-1:0]    m_ram [0:(1<<ADDRESS_WIDTH)-1]
);

  localparam int DW = DATA_WIDTH-1;
  localparam int AW = ADDRESS_WIDTH-1;

  // past-valid flags
  bit pastA, pastB;
  always_ff @(posedge clka) pastA <= 1'b1;
  always_ff @(posedge clkb) pastB <= 1'b1;

  // 1) Sanity on known controls/inputs
  a_wea_known:      assert property (@(posedge clka) !$isunknown(wea));
  a_write_inputs_ok:assert property (@(posedge clka) wea |-> !$isunknown({addra,dina}));
  a_addrb_known:    assert property (@(posedge clkb) !$isunknown(addrb));

  // 2) Write-port: update and no-spurious-update semantics (clka domain)
  a_wr_update:      assert property (@(posedge clka) pastA && $past(wea)
                                     |-> m_ram[$past(addra)] == $past(dina));
  a_wr_no_update:   assert property (@(posedge clka) pastA && !$past(wea)
                                     |-> m_ram[$past(addra)] == $past(m_ram[$past(addra)]));

  // 3) Read-port: registered read from RAM (clkb domain)
  a_rd_matches_ram: assert property (@(posedge clkb) pastB
                                     |-> doutb == $past(m_ram[$past(addrb)]));

  // 4) doutb only changes on clkb rising edge
  a_doutb_edges:    assert property (@(doutb) $rose(clkb));

  // 5) If address is stable and no write to that address occurred between clkb edges, doutb is stable
  logic [AW:0] addrb_q;
  bit          primedB, wr_between;
  always_ff @(posedge clkb) begin
    addrb_q     <= addrb;
    wr_between  <= 1'b0;
    primedB     <= 1'b1;
  end
  always_ff @(posedge clka) begin
    if (primedB && wea && (addra == addrb_q)) wr_between <= 1'b1;
  end
  a_no_change_without_write: assert property (@(posedge clkb)
                               primedB && (addrb == $past(addrb)) && !wr_between
                               |-> doutb == $past(doutb));

  // 6) Useful coverage
  c_write_any:      cover property (@(posedge clka) wea);
  c_read_toggles:   cover property (@(posedge clkb) $changed(doutb));
  c_wr_min_addr:    cover property (@(posedge clka) wea && (addra == '0));
  c_wr_max_addr:    cover property (@(posedge clka) wea && (&addra));

  // write followed by a read of the same address at some later clkb edge
  property c_wr_then_rd_same_addr;
    logic [AW:0] a;
    @(posedge clka) (wea, a = addra)
      |-> ##[1:$] @(posedge clkb) (addrb == a);
  endproperty
  cover property (c_wr_then_rd_same_addr);

endmodule

// Bind into DUT
bind ad_mem ad_mem_sva #(.DATA_WIDTH(DATA_WIDTH), .ADDRESS_WIDTH(ADDRESS_WIDTH)) ad_mem_sva_i (
  .clka(clka),
  .wea(wea),
  .addra(addra),
  .dina(dina),
  .clkb(clkb),
  .addrb(addrb),
  .doutb(doutb),
  .m_ram(m_ram)
);