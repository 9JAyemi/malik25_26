// SVA checker for MMU_MATCH
// Bind into the DUT and provide a clock/reset from TB/formal env.
// Focuses on combinational correctness, key gating, and targeted coverage.

module mmu_match_sva #(parameter bit USE_RESET = 1) (
  input logic clk,
  input logic rst_n
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (USE_RESET ? !rst_n : 1'b0);

  // Local re-computations (purely from DUT visible signals)
  let maske_exp    = (16'h0001 << VADR_R[15:12]);
  let zugriff_exp  = (READ | WRITE);
  let virt_exp     = (USER ? MCR_FLAGS[0] : MCR_FLAGS[1]);
  let adr_space_exp= (IVAR[1] ? IVAR[0] : (MCR_FLAGS[2] & USER));
  let as_sorte_exp = ((MVALID[31:16] & maske) != 16'h0);
  let match_exp    = (VADR_R[31:20] == MMU_VA[31:20]) &&
                     (adr_space == as_sorte) &&
                     ((MVALID[15:0] & maske) != 16'h0000);
  let pe_exp = (ena_prot && (MMU_VA[19:18]==2'b00)) ? (USER | WRITE | RMW) :
               (ena_prot && (MMU_VA[19:18]==2'b01)) ? (USER) :
               (ena_prot && (MMU_VA[19:18]==2'b10)) ? (USER & (WRITE | RMW)) :
               1'b0;
  let alles_ok_exp = match & (~WRITE | MMU_VA[17]) & ~PROT_ERROR;
  let hit_exp      = zugriff ? (VIRTUELL ? alles_ok : 1'b1) : 1'b0;
  let val_bits_exp = IVAR[1] ? (MVALID[15:0] & (match ? ~maske : 16'hFFFF))
                             : (MVALID[15:0] | maske);
  let as_bits_exp  = IVAR[1] ? MVALID[31:16]
                             : (adr_space ? (MVALID[31:16] | maske)
                                          : (MVALID[31:16] & ~maske));
  let update_exp   = {as_bits, val_bits};
  let ci_exp       = VIRTUELL & MMU_VA[16];

  // Structural/encoding checks
  assert property (maske == maske_exp);
  assert property ($onehot(maske));

  // Internal wire/functionality equivalence
  assert property (VIRTUELL   == virt_exp);
  assert property (adr_space  == adr_space_exp);
  assert property (as_sorte   == as_sorte_exp);
  assert property (match      == match_exp);
  assert property (ena_prot   == (zugriff & VIRTUELL & match));
  assert property (alles_ok   == alles_ok_exp);

  // Outputs consistency
  assert property (MMU_HIT    == hit_exp);
  assert property (val_bits   == val_bits_exp);
  assert property (as_bits    == as_bits_exp);
  assert property (UPDATE     == update_exp);
  assert property (CI         == ci_exp);
  assert property (SEL_PTB1   == adr_space);

  // Protection logic
  assert property (PROT_ERROR == pe_exp);
  assert property (!ena_prot |-> !PROT_ERROR);
  // RMW alone is not a "zugriff" => no protection engagement
  assert property (RMW & !READ & !WRITE |-> !ena_prot && !PROT_ERROR);

  // Targeted functional assertions
  // Physical access forces hit on any access
  assert property (zugriff & !VIRTUELL |-> MMU_HIT);
  // Virtual write requires MMU_VA[17]==1 and no PROT_ERROR to hit
  assert property (zugriff & VIRTUELL & match & WRITE & !PROT_ERROR & !MMU_VA[17] |-> !MMU_HIT);
  assert property (zugriff & VIRTUELL & match & WRITE & !PROT_ERROR &  MMU_VA[17] |->  MMU_HIT);

  // Coverage: key modes, protection cases, update behaviors
  cover property (zugriff & !VIRTUELL & MMU_HIT);                        // physical hit
  cover property (READ & VIRTUELL & match & !WRITE & !PROT_ERROR & MMU_HIT); // virtual read hit
  cover property (WRITE & VIRTUELL & match &  MMU_VA[17] & !PROT_ERROR & MMU_HIT); // allowed write
  cover property (WRITE & VIRTUELL & match & !MMU_VA[17] & !MMU_HIT);    // blocked write
  cover property (ena_prot && (MMU_VA[19:18]==2'b00) && PROT_ERROR);
  cover property (ena_prot && (MMU_VA[19:18]==2'b01) && USER && PROT_ERROR);
  cover property (ena_prot && (MMU_VA[19:18]==2'b10) && USER && (WRITE|RMW) && PROT_ERROR);
  cover property (IVAR[1]==1'b0 && adr_space && (UPDATE[31:16]==(MVALID[31:16]|maske))); // as_bits OR path
  cover property (IVAR[1]==1'b0 && !adr_space && (UPDATE[31:16]==(MVALID[31:16]&~maske))); // as_bits AND path
  cover property (IVAR[1]==1'b1 && match && (UPDATE[15:0]==(MVALID[15:0]&~maske)));  // val_bits clear on match
  cover property (IVAR[1]==1'b1 && !match && (UPDATE[15:0]==MVALID[15:0]));           // val_bits unchanged
  cover property (VADR_R[15:12]==4'h0 && maske==16'h0001);
  cover property (VADR_R[15:12]==4'hF && maske==16'h8000);

endmodule

// Example bind (instantiate once per DUT instance)
// In your TB/top, drive clk/rst_n appropriately.
// bind MMU_MATCH mmu_match_sva u_mmu_match_sva(.clk(tb_clk), .rst_n(tb_rst_n));