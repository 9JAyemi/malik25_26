// SystemVerilog Assertions for rcn_slave
module rcn_slave_sva
  #(parameter int unsigned ADDR_MASK = 0,
    parameter int unsigned ADDR_BASE = 1)
(
    input  logic        rst,
    input  logic        clk,

    input  logic [68:0] rcn_in,
    input  logic [68:0] rcn_out,

    input  logic        cs,
    input  logic        wr,
    input  logic [3:0]  mask,
    input  logic [23:0] addr,
    input  logic [31:0] wdata,
    input  logic [31:0] rdata
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  function automatic bit hit(input logic [68:0] v);
    hit = v[68] && v[67] && ((v[55:34] & ADDR_MASK[23:2]) == ADDR_BASE[23:2]);
  endfunction

  // Input-to-sideband mapping (1-cycle latency)
  ap_cs_eq:     assert property ($past(!rst)     |-> cs    == hit($past(rcn_in)));
  ap_wr_eq:     assert property ($past(!rst)     |-> wr    == $past(rcn_in[66]));
  ap_mask_eq:   assert property ($past(!rst)     |-> mask  == $past(rcn_in[59:56]));
  ap_addr_eq:   assert property ($past(!rst)     |-> addr  == {$past(rcn_in[55:34]), 2'b00});
  ap_addr_lsb0: assert property (addr[1:0] == 2'b00);
  ap_wdata_eq:  assert property ($past(!rst)     |-> wdata == $past(rcn_in[31:0]));

  // Output behavior (2/3-cycle latency)
  // Miss: forward old input
  ap_fwd_path:  assert property ($past(!rst,2) && !$past(cs,2)
                                 |-> rcn_out == $past(rcn_in,2));

  // Hit: form response = {1,0, old header, old rdata}
  ap_resp_path: assert property ($past(!rst,3) && $past(cs,2)
                                 |-> rcn_out == {1'b1, 1'b0, $past(rcn_in,3)[66:32], $past(rdata)});
  ap_resp_flags: assert property ($past(!rst,3) && $past(cs,2)
                                  |-> rcn_out[68] == 1'b1 && rcn_out[67] == 1'b0);

  // Reset behavior (observed on clock)
  ap_reset_zero: assert property (rst |-> rcn_out == 69'd0 && cs == 1'b0 && wr == 1'b0);

  // Coverage
  cp_hit:      cover property ($past(!rst)   && hit($past(rcn_in)));
  cp_miss:     cover property ($past(!rst)   && !hit($past(rcn_in)));
  cp_read_req: cover property ($past(!rst)   && hit($past(rcn_in)) && !$past(rcn_in[66]));
  cp_write_req:cover property ($past(!rst)   && hit($past(rcn_in)) &&  $past(rcn_in[66]));
  cp_resp:     cover property ($past(!rst,3) && $past(cs,2));
  cp_forward:  cover property ($past(!rst,2) && !$past(cs,2));

endmodule

// Bind into DUT
bind rcn_slave rcn_slave_sva #(.ADDR_MASK(ADDR_MASK), .ADDR_BASE(ADDR_BASE)) rcn_slave_sva_i (
  .rst, .clk, .rcn_in, .rcn_out, .cs, .wr, .mask, .addr, .wdata, .rdata
);