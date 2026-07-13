module ded_ca_top_sva
  #(parameter BYTES = 4)
  (
    input logic mclock,
    input logic mc_push,
`ifdef BYTE16
    input logic [2:0] mc_addr,
`elsif BYTE8
    input logic [3:0] mc_addr,
`else
    input logic [4:0] mc_addr,
`endif

    input logic hclock,
    input logic hb_we,
    input logic [4:0] hb_addr,
    input logic [(BYTES*8)-1:0] hb_dout_ram,

`ifdef BYTE16
    input logic [2:0] rad,
`elsif BYTE8
    input logic [3:0] rad,
`else
    input logic [4:0] rad,
`endif

`ifdef BYTE16
    input logic [3:0] ca_enable,
`elsif BYTE8
    input logic [1:0] ca_enable,
`else
    input logic       ca_enable,
`endif
    input logic [31:0] hb_dout,
    input logic [4:0]  hb_ram_addr,
    input logic [4:0]  ca_ram_addr0,
    input logic [4:0]  ca_ram_addr1
  );

`ifdef BYTE16

  // hb_dout selects a 32-bit lane from hb_dout_ram using hb_addr[1:0].
  check_hb_dout_lane_select: assert property (
    @(posedge hclock)
    hb_dout == hb_dout_ram[hb_addr[1:0]*32 +: 32]
  );

  // ca_enable decodes hb_we into a one-hot byte-group enable.
  check_ca_enable_decode: assert property (
    @(posedge hclock)
    ca_enable == {
      (hb_we & (hb_addr[1:0] == 2'd3)),
      (hb_we & (hb_addr[1:0] == 2'd2)),
      (hb_we & (hb_addr[1:0] == 2'd1)),
      (hb_we & (hb_addr[1:0] == 2'd0))
    }
  );

  // hb_ram_addr zero-extends hb_addr[4:2].
  check_hb_ram_addr_map: assert property (
    @(posedge hclock)
    hb_ram_addr == {2'b0, hb_addr[4:2]}
  );

  // ca_ram_addr0 selects mc_addr on push, otherwise rad.
  check_ca_ram_addr0_select: assert property (
    @(posedge mclock)
    ca_ram_addr0 == (mc_push ? {2'b0, mc_addr} : {2'b0, rad})
  );

  // ca_ram_addr1 selects mc_addr on push, otherwise rad plus one.
  check_ca_ram_addr1_select: assert property (
    @(posedge mclock)
    ca_ram_addr1 == (mc_push ? {2'b0, mc_addr} : {2'b0, (rad + 3'h1)})
  );

  // During push, both CA RAM addresses match mc_addr.
  check_ca_ram_addrs_match_on_push: assert property (
    @(posedge mclock)
    mc_push |-> ((ca_ram_addr0 == {2'b0, mc_addr}) && (ca_ram_addr1 == {2'b0, mc_addr}))
  );

`elsif BYTE8

  // hb_dout selects a 32-bit lane from hb_dout_ram using hb_addr[0].
  check_hb_dout_lane_select: assert property (
    @(posedge hclock)
    hb_dout == hb_dout_ram[hb_addr[0]*32 +: 32]
  );

  // ca_enable decodes hb_we into a one-hot byte-group enable.
  check_ca_enable_decode: assert property (
    @(posedge hclock)
    ca_enable == {
      (hb_we & (hb_addr[0] == 1'b1)),
      (hb_we & (hb_addr[0] == 1'b0))
    }
  );

  // hb_ram_addr zero-extends hb_addr[4:1].
  check_hb_ram_addr_map: assert property (
    @(posedge hclock)
    hb_ram_addr == {1'b0, hb_addr[4:1]}
  );

  // ca_ram_addr0 selects mc_addr on push, otherwise rad.
  check_ca_ram_addr0_select: assert property (
    @(posedge mclock)
    ca_ram_addr0 == (mc_push ? {1'b0, mc_addr} : {1'b0, rad})
  );

  // ca_ram_addr1 selects mc_addr on push, otherwise rad plus one.
  check_ca_ram_addr1_select: assert property (
    @(posedge mclock)
    ca_ram_addr1 == (mc_push ? {1'b0, mc_addr} : {1'b0, (rad + 4'h1)})
  );

  // During push, both CA RAM addresses match mc_addr.
  check_ca_ram_addrs_match_on_push: assert property (
    @(posedge mclock)
    mc_push |-> ((ca_ram_addr0 == {1'b0, mc_addr}) && (ca_ram_addr1 == {1'b0, mc_addr}))
  );

`else

  // hb_dout passes through the low 32 bits of hb_dout_ram.
  check_hb_dout_passthrough: assert property (
    @(posedge hclock)
    hb_dout == hb_dout_ram[31:0]
  );

  // ca_enable matches hb_we directly.
  check_ca_enable_passthrough: assert property (
    @(posedge hclock)
    ca_enable == hb_we
  );

  // hb_ram_addr matches hb_addr directly.
  check_hb_ram_addr_map: assert property (
    @(posedge hclock)
    hb_ram_addr == hb_addr[4:0]
  );

  // ca_ram_addr0 selects mc_addr on push, otherwise rad.
  check_ca_ram_addr0_select: assert property (
    @(posedge mclock)
    ca_ram_addr0 == (mc_push ? mc_addr : rad)
  );

  // ca_ram_addr1 selects mc_addr on push, otherwise rad plus one.
  check_ca_ram_addr1_select: assert property (
    @(posedge mclock)
    ca_ram_addr1 == (mc_push ? mc_addr : (rad + 5'h1))
  );

  // During push, both CA RAM addresses match mc_addr.
  check_ca_ram_addrs_match_on_push: assert property (
    @(posedge mclock)
    mc_push |-> ((ca_ram_addr0 == mc_addr) && (ca_ram_addr1 == mc_addr))
  );

`endif

endmodule