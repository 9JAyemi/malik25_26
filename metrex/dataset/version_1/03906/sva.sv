// SVA for load_store_pipe_arbiter
bind load_store_pipe_arbiter load_store_pipe_arbiter_sva();

module load_store_pipe_arbiter_sva;

  // Optional global clock for cover; assertions are immediate (combinational)
  default clocking cb @ (posedge $global_clock); endclocking

  // Combinational equivalence checks (golden truth-table for the mux/steering)
  always_comb begin
    assert (oLDST_REQ   == (iUSE_SEL ? iEXCEPT_REQ   : iEXE_REQ))    else $error("oLDST_REQ mux");
    assert (oLDST_ORDER == (iUSE_SEL ? iEXCEPT_ORDER : iEXE_ORDER))  else $error("oLDST_ORDER mux");
    assert (oLDST_MASK  == (iUSE_SEL ? 4'hf          : iEXE_MASK))   else $error("oLDST_MASK mux/force");
    assert (oLDST_RW    == (iUSE_SEL ? iEXCEPT_RW    : iEXE_RW))     else $error("oLDST_RW mux");
    assert (oLDST_ASID  == (iUSE_SEL ? iEXCEPT_ASID  : iEXE_ASID))   else $error("oLDST_ASID mux");
    assert (oLDST_MMUMOD== (iUSE_SEL ? iEXCEPT_MMUMOD: iEXE_MMUMOD)) else $error("oLDST_MMUMOD mux");
    assert (oLDST_MMUPS == (iUSE_SEL ? iEXCEPT_MMUPS : iEXE_MMUPS))  else $error("oLDST_MMUPS mux");
    assert (oLDST_PDT   == (iUSE_SEL ? iEXCEPT_PDT   : iEXE_PDT))    else $error("oLDST_PDT mux");
    assert (oLDST_ADDR  == (iUSE_SEL ? iEXCEPT_ADDR  : iEXE_ADDR))   else $error("oLDST_ADDR mux");
    assert (oLDST_DATA  == (iUSE_SEL ? iEXCEPT_DATA  : iEXE_DATA))   else $error("oLDST_DATA mux");

    assert (oEXCEPT_BUSY == (iUSE_SEL ? iLDST_BUSY   : 1'b1))        else $error("oEXCEPT_BUSY steer");
    assert (oEXCEPT_REQ  == (iUSE_SEL ? iLDST_VALID  : 1'b0))        else $error("oEXCEPT_REQ steer");
    assert (oEXCEPT_DATA == iLDST_DATA)                              else $error("oEXCEPT_DATA passthru");

    assert (oEXE_BUSY    == (iUSE_SEL ? 1'b1         : iLDST_BUSY))  else $error("oEXE_BUSY steer");
    assert (oEXE_REQ     == (iUSE_SEL ? 1'b0         : iLDST_VALID)) else $error("oEXE_REQ steer");
    assert (oEXE_MMU_FLAGS == iLDST_MMU_FLAGS)                       else $error("oEXE_MMU_FLAGS passthru");
    assert (oEXE_DATA    == iLDST_DATA)                              else $error("oEXE_DATA passthru");
  end

  // X/unknown safety when relevant drivers are known
  always_comb begin
    if (!$isunknown({iUSE_SEL,iEXE_REQ,iEXCEPT_REQ}))
      assert (!$isunknown(oLDST_REQ)) else $error("X on oLDST_REQ");
    if (!$isunknown(iLDST_DATA)) begin
      assert (!$isunknown(oEXE_DATA))    else $error("X on oEXE_DATA");
      assert (!$isunknown(oEXCEPT_DATA)) else $error("X on oEXCEPT_DATA");
    end
    if (!$isunknown(iLDST_MMU_FLAGS))
      assert (!$isunknown(oEXE_MMU_FLAGS)) else $error("X on oEXE_MMU_FLAGS");
  end

  // Minimal functional coverage to exercise both paths and key behaviors
  cover property (!iUSE_SEL);
  cover property ( iUSE_SEL);
  cover property (!iUSE_SEL && iLDST_VALID && (oEXE_REQ==1));
  cover property ( iUSE_SEL && iLDST_VALID && (oEXCEPT_REQ==1));
  cover property (!iUSE_SEL && oLDST_REQ && (oLDST_RW==iEXE_RW));
  cover property ( iUSE_SEL && oLDST_REQ && (oLDST_RW==iEXCEPT_RW));
  cover property ( iUSE_SEL && (oLDST_MASK==4'hf));

endmodule