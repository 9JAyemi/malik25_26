// SVA for sha512_w_mem
// Bind this module to the DUT: bind sha512_w_mem sha512_w_mem_sva sva();

module sha512_w_mem_sva;

  // Access DUT scope via bind; assumes these names exist in sha512_w_mem
  // clk, reset_n, block, init, next, w
  // w_mem[0:15], w_mem_we, w_ctr_reg, w_ctr_new, w_ctr_we, w_new, w_tmp

  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset_n);

  // Helpers
  function automatic [63:0] ror64(input [63:0] x, input int unsigned n);
    ror64 = (x >> n) | (x << (64 - n));
  endfunction

  // Reset behavior
  assert property (!reset_n |-> (w_ctr_reg == 7'h00
                                && w_mem[0]  == 64'h0 && w_mem[1]  == 64'h0
                                && w_mem[2]  == 64'h0 && w_mem[3]  == 64'h0
                                && w_mem[4]  == 64'h0 && w_mem[5]  == 64'h0
                                && w_mem[6]  == 64'h0 && w_mem[7]  == 64'h0
                                && w_mem[8]  == 64'h0 && w_mem[9]  == 64'h0
                                && w_mem[10] == 64'h0 && w_mem[11] == 64'h0
                                && w_mem[12] == 64'h0 && w_mem[13] == 64'h0
                                && w_mem[14] == 64'h0 && w_mem[15] == 64'h0));

  // Counter control/gating and update semantics
  assert property (w_ctr_we == (init || next));
  assert property (w_ctr_new == (next ? (w_ctr_reg + 7'h01) : (init ? 7'h00 : 7'h00)));
  assert property ( w_ctr_we |=> (w_ctr_reg == $past(w_ctr_new)) );
  assert property (!w_ctr_we |=> (w_ctr_reg == $past(w_ctr_reg)));

  // w_new combinational correctness (σ0/σ1 per FIPS 180-4)
  assert property ( w_new == ( w_mem[0]
                             + ( ror64(w_mem[1],1)  ^ ror64(w_mem[1],8)  ^ (w_mem[1]  >> 7) )
                             +   w_mem[9]
                             + ( ror64(w_mem[14],19) ^ ror64(w_mem[14],61) ^ (w_mem[14] >> 6) ) ) );

  // Output mux correctness
  assert property ((w_ctr_reg < 7'd16) |-> (w == w_mem[w_ctr_reg[3:0]]));
  assert property ((w_ctr_reg >= 7'd16) |-> (w == w_new));

  // Write enable gating
  assert property (w_mem_we == (init || (next && (w_ctr_reg > 7'd15))));

  // No-write holds memory
  assert property (!w_mem_we |=> ( w_mem[0]  == $past(w_mem[0])  && w_mem[1]  == $past(w_mem[1])  &&
                                   w_mem[2]  == $past(w_mem[2])  && w_mem[3]  == $past(w_mem[3])  &&
                                   w_mem[4]  == $past(w_mem[4])  && w_mem[5]  == $past(w_mem[5])  &&
                                   w_mem[6]  == $past(w_mem[6])  && w_mem[7]  == $past(w_mem[7])  &&
                                   w_mem[8]  == $past(w_mem[8])  && w_mem[9]  == $past(w_mem[9])  &&
                                   w_mem[10] == $past(w_mem[10]) && w_mem[11] == $past(w_mem[11]) &&
                                   w_mem[12] == $past(w_mem[12]) && w_mem[13] == $past(w_mem[13]) &&
                                   w_mem[14] == $past(w_mem[14]) && w_mem[15] == $past(w_mem[15]) ));

  // Init load path (init takes priority for mem when w_ctr_reg <= 15)
  assert property ( (init && !(next && (w_ctr_reg > 7'd15))) |=> (
                      w_mem[0]  == $past(block[1023:960]) &&
                      w_mem[1]  == $past(block[959:896])  &&
                      w_mem[2]  == $past(block[895:832])  &&
                      w_mem[3]  == $past(block[831:768])  &&
                      w_mem[4]  == $past(block[767:704])  &&
                      w_mem[5]  == $past(block[703:640])  &&
                      w_mem[6]  == $past(block[639:576])  &&
                      w_mem[7]  == $past(block[575:512])  &&
                      w_mem[8]  == $past(block[511:448])  &&
                      w_mem[9]  == $past(block[447:384])  &&
                      w_mem[10] == $past(block[383:320])  &&
                      w_mem[11] == $past(block[319:256])  &&
                      w_mem[12] == $past(block[255:192])  &&
                      w_mem[13] == $past(block[191:128])  &&
                      w_mem[14] == $past(block[127:64])   &&
                      w_mem[15] == $past(block[63:0]) ));

  // Next/expand path with sliding window (next overrides init for mem when w_ctr_reg > 15)
  assert property ( (next && (w_ctr_reg > 7'd15)) |=> (
                      w_mem[0]  == $past(w_mem[1])  &&
                      w_mem[1]  == $past(w_mem[2])  &&
                      w_mem[2]  == $past(w_mem[3])  &&
                      w_mem[3]  == $past(w_mem[4])  &&
                      w_mem[4]  == $past(w_mem[5])  &&
                      w_mem[5]  == $past(w_mem[6])  &&
                      w_mem[6]  == $past(w_mem[7])  &&
                      w_mem[7]  == $past(w_mem[8])  &&
                      w_mem[8]  == $past(w_mem[9])  &&
                      w_mem[9]  == $past(w_mem[10]) &&
                      w_mem[10] == $past(w_mem[11]) &&
                      w_mem[11] == $past(w_mem[12]) &&
                      w_mem[12] == $past(w_mem[13]) &&
                      w_mem[13] == $past(w_mem[14]) &&
                      w_mem[14] == $past(w_mem[15]) &&
                      w_mem[15] == $past(w_new) ));

  // Coverage
  cover property (init);
  cover property (next && (w_ctr_reg == 7'd15));
  cover property (next && (w_ctr_reg > 7'd15));
  cover property (init && next && (w_ctr_reg <= 7'd15));
  cover property (init && next && (w_ctr_reg > 7'd15));
  cover property ((w_ctr_reg == 7'h7f) ##1 next ##1 (w_ctr_reg == 7'h00));

endmodule

// Bind into the DUT
bind sha512_w_mem sha512_w_mem_sva sva();