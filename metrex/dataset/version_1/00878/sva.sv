// SVA for SP_RAM_32x512 and BRAM_SDP_32x512
`ifndef SYNTHESIS
module SP_RAM_32x512_sva #(parameter AWIDTH=9, DWIDTH=32);
  localparam DEPTH = 1<<AWIDTH;

  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Simple reference model at the interface (captures RTL's read-before-write behavior)
  logic [DWIDTH-1:0] ref_mem [0:DEPTH-1];
  always_ff @(posedge clk) if (wce) ref_mem[wa] <= wd;

  default clocking cb @(posedge clk); endclocking

  // Sanity / X checks
  assert property (disable iff (!past_valid) !$isunknown({rce,wce}));
  assert property (disable iff (!past_valid) rce |-> !$isunknown(ra));
  assert property (disable iff (!past_valid) wce |-> !$isunknown({wa,wd}));

  // Top wrapper behavior: gated register of BRAM output
  assert property (disable iff (!past_valid) !rce |=> rq == $past(rq));
  assert property (disable iff (!past_valid)  rce |=> rq == $past(bram_out));

  // BRAM read semantics (read returns OLD data if read/write same cycle)
  assert property (disable iff (!past_valid) rce |-> BRAM_32x512.rq == $past(ref_mem[ra]));

  // Write data mux correctness into BRAM
  assert property (bram_in == (wce ? wd : {DWIDTH{1'b0}}));

  // Connectivity checks to BRAM instance
  assert property (rce == BRAM_32x512.rce);
  assert property (wce == BRAM_32x512.wce);
  assert property (ra  == BRAM_32x512.ra);
  assert property (wa  == BRAM_32x512.wa);
  assert property (bram_in == BRAM_32x512.wd);

  // Coverage
  cover property (wce);
  cover property (rce);
  cover property (rce && wce);
  cover property (rce && wce && (ra==wa));                 // same-cycle RAW hazard exercised
  cover property (wce && wa==0);
  cover property (wce && wa==DEPTH-1);
  cover property (rce && ra==0);
  cover property (rce && ra==DEPTH-1);
  cover property (wce && (wd=='0));
  cover property (wce && (wd=={DWIDTH{1'b1}}));
  // End-to-end pipeline: write A, then read A with 2-cycle rce pipeline
  cover property (wce ##1 (rce && (ra==wa)) ##1 rce);
endmodule

bind SP_RAM_32x512 SP_RAM_32x512_sva #(.AWIDTH(AWIDTH), .DWIDTH(DWIDTH)) u_SP_RAM_32x512_sva();
`endif