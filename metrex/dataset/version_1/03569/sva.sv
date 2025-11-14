// SVA checker for win_blk_mem_gen_prim_width
// Concise, bindable, with shadow model and key properties

module win_blk_mem_gen_prim_width_sva (
  input  logic         clka,
  input  logic [13:0]  addra,
  input  logic [0:0]   dina,
  input  logic [0:0]   wea,
  input  logic [0:0]   douta
);

  // Shadow memory model + valid map
  logic [0:0] shadow_mem [0:16383];
  bit         valid      [0:16383];
  bit         started;

  always_ff @(posedge clka) begin
    started <= 1'b1;
    if (!$isunknown(wea[0]) && wea[0]) begin
      shadow_mem[addra] <= dina;
      valid[addra]      <= 1'b1;
    end
  end

  default clocking cb @(posedge clka); endclocking

  // Basic sanity of controls (no X/Z)
  assert property (started |-> !$isunknown(wea[0])) else $error("wea is X/Z");
  assert property (started |-> !$isunknown(addra)) else $error("addra has X/Z bits");

  // Data sanity on write
  assert property (started && wea[0] |-> !$isunknown(dina)) else $error("dina is X/Z during write");

  // Write cycle: douta holds its previous value (no read during write)
  assert property (started && !$isunknown(wea[0]) && wea[0] |-> $stable(douta))
    else $error("douta changed on a write cycle");

  // Read cycle: douta reflects stored data (when address has been written before)
  // Use ##0 to avoid region races and compare post-NBA douta to pre-NBA shadow_mem
  assert property (started && !$isunknown(wea[0]) && !wea[0] && valid[addra] |-> ##0 (douta == shadow_mem[addra]))
    else $error("Read data mismatch");

  // Consecutive reads to same address return same value (no intervening write)
  assert property (started && !wea[0] && $past(!wea[0]) && (addra == $past(addra)) |-> (douta == $past(douta)))
    else $error("Consecutive read mismatch on same address");

  // Coverage: basic access patterns
  cover property (started && wea[0]);                               // saw a write
  cover property (started && !wea[0]);                              // saw a read
  cover property (started && wea[0] ##1 (!wea[0] && addra == $past(addra))); // write then read same addr next cycle
  cover property (started && wea[0] ##1 wea[0]);                    // back-to-back writes
  cover property (started && !wea[0] ##1 !wea[0]);                  // back-to-back reads
  cover property (started && !wea[0] ##1 (!wea[0] && addra != $past(addra))); // reads to different addrs

endmodule

// Bind into DUT
bind win_blk_mem_gen_prim_width
  win_blk_mem_gen_prim_width_sva u_win_blk_mem_gen_prim_width_sva (
    .clka  (clka),
    .addra (addra),
    .dina  (dina),
    .wea   (wea),
    .douta (douta)
  );