// SVA for sha1_w_mem
// Bind this module to the DUT:
//   bind sha1_w_mem sha1_w_mem_sva sva();

module sha1_w_mem_sva;

  // Access DUT scope via bind
  // clk, reset_n, block, init, next, w, w_mem[], w_mem_we, w_ctr_reg, w_ctr_we

  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset_n);

  function automatic [31:0] rol1(input [31:0] x);
    return {x[30:0], x[31]};
  endfunction

  // Illegal: init and next in same cycle (prevents priority artifacts)
  assert property (!(init && next));

  // w_ctr write enable coherence
  assert property (w_ctr_we |-> (init || next));
  assert property ((!init && !next) |-> !w_ctr_we);

  // Counter updates
  assert property ($past(reset_n) && init |=> w_ctr_reg == 7'd0);
  assert property ($past(reset_n) && next |=> w_ctr_reg == $past(w_ctr_reg) + 7'd1);

  // w_mem write enable coherence
  assert property (w_mem_we |-> (init || (next && (w_ctr_reg > 7'd15))));
  assert property (init |-> w_mem_we);
  assert property ((next && (w_ctr_reg > 7'd15)) |-> w_mem_we);
  assert property ((next && (w_ctr_reg <= 7'd15)) |-> !w_mem_we);

  // w_mem must not change without write enable
  genvar gi;
  generate
    for (gi = 0; gi < 16; gi++) begin : g_mem_stable
      assert property ($past(reset_n) && !$past(w_mem_we) |-> w_mem[gi] == $past(w_mem[gi]));
    end
  endgenerate

  // Init loads block into w_mem (word/bit mapping)
  assert property ($past(reset_n) && init |=> w_mem[ 0] == $past(block[511:480]));
  assert property ($past(reset_n) && init |=> w_mem[ 1] == $past(block[479:448]));
  assert property ($past(reset_n) && init |=> w_mem[ 2] == $past(block[447:416]));
  assert property ($past(reset_n) && init |=> w_mem[ 3] == $past(block[415:384]));
  assert property ($past(reset_n) && init |=> w_mem[ 4] == $past(block[383:352]));
  assert property ($past(reset_n) && init |=> w_mem[ 5] == $past(block[351:320]));
  assert property ($past(reset_n) && init |=> w_mem[ 6] == $past(block[319:288]));
  assert property ($past(reset_n) && init |=> w_mem[ 7] == $past(block[287:256]));
  assert property ($past(reset_n) && init |=> w_mem[ 8] == $past(block[255:224]));
  assert property ($past(reset_n) && init |=> w_mem[ 9] == $past(block[223:192]));
  assert property ($past(reset_n) && init |=> w_mem[10] == $past(block[191:160]));
  assert property ($past(reset_n) && init |=> w_mem[11] == $past(block[159:128]));
  assert property ($past(reset_n) && init |=> w_mem[12] == $past(block[127:96]));
  assert property ($past(reset_n) && init |=> w_mem[13] == $past(block[95:64]));
  assert property ($past(reset_n) && init |=> w_mem[14] == $past(block[63:32]));
  assert property ($past(reset_n) && init |=> w_mem[15] == $past(block[31:0]));

  // next when ctr>15: shift window and compute new word
  assert property (
    $past(reset_n) && (next && (w_ctr_reg > 7'd15)) |=> (
      (w_mem[ 0] == $past(w_mem[ 1])) &&
      (w_mem[ 1] == $past(w_mem[ 2])) &&
      (w_mem[ 2] == $past(w_mem[ 3])) &&
      (w_mem[ 3] == $past(w_mem[ 4])) &&
      (w_mem[ 4] == $past(w_mem[ 5])) &&
      (w_mem[ 5] == $past(w_mem[ 6])) &&
      (w_mem[ 6] == $past(w_mem[ 7])) &&
      (w_mem[ 7] == $past(w_mem[ 8])) &&
      (w_mem[ 8] == $past(w_mem[ 9])) &&
      (w_mem[ 9] == $past(w_mem[10])) &&
      (w_mem[10] == $past(w_mem[11])) &&
      (w_mem[11] == $past(w_mem[12])) &&
      (w_mem[12] == $past(w_mem[13])) &&
      (w_mem[13] == $past(w_mem[14])) &&
      (w_mem[14] == $past(w_mem[15])) &&
      (w_mem[15] == rol1($past(w_mem[13] ^ w_mem[8] ^ w_mem[2] ^ w_mem[0])))
    )
  );

  // w output checks in cycles without memory write (avoids sampling race)
  // If ctr<16 and no mem write last cycle, w should reflect selected word
  assert property (
    $past(reset_n) && ($past(w_ctr_reg) < 7'd16) && !$past(w_mem_we)
    |-> w == $past(w_mem[$past(w_ctr_reg[3:0])])
  );

  // If ctr>15 and no mem write last cycle, w should be rol1(xor of 13,8,2,0)
  assert property (
    $past(reset_n) && ($past(w_ctr_reg) > 7'd15) && !$past(w_mem_we)
    |-> w == rol1($past(w_mem[13] ^ w_mem[8] ^ w_mem[2] ^ w_mem[0]))
  );

  // Reset behavior: during reset, regs cleared
  assert property (disable iff (1'b0) !reset_n |-> (w_ctr_reg == 7'd0
    && (w_mem[0]==32'h0 && w_mem[1]==32'h0 && w_mem[2]==32'h0 && w_mem[3]==32'h0
    && w_mem[4]==32'h0 && w_mem[5]==32'h0 && w_mem[6]==32'h0 && w_mem[7]==32'h0
    && w_mem[8]==32'h0 && w_mem[9]==32'h0 && w_mem[10]==32'h0 && w_mem[11]==32'h0
    && w_mem[12]==32'h0 && w_mem[13]==32'h0 && w_mem[14]==32'h0 && w_mem[15]==32'h0)));

  // Coverage
  cover property (init);
  cover property (next && (w_ctr_reg < 7'd16));
  cover property (next && (w_ctr_reg > 7'd15));
  cover property (init ##1 next[*20]); // exercise ctr advance across boundary

endmodule

bind sha1_w_mem sha1_w_mem_sva sva();