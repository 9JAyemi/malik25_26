// SVA for axis_packetizer
// Bind this file to the DUT:
//   bind axis_packetizer axis_packetizer_sva #(.AXIS_TDATA_WIDTH(AXIS_TDATA_WIDTH), .CNTR_WIDTH(CNTR_WIDTH), .CONTINUOUS(CONTINUOUS), .ALWAYS_READY(ALWAYS_READY)) sva ();

// Assertions focus on functional correctness, handshakes, counter, enable, TLAST/TVALID relations, and mode-specific behavior.
module axis_packetizer_sva #(
  parameter int AXIS_TDATA_WIDTH = 32,
  parameter int CNTR_WIDTH       = 32,
  parameter string CONTINUOUS    = "FALSE",
  parameter string ALWAYS_READY  = "FALSE"
);
  default clocking cb @(posedge aclk); endclocking
  default disable iff (!aresetn)

  // Basic reset state for key regs/outs
  assert property (!aresetn |-> (int_cntr_reg == '0 && int_enbl_reg == 1'b0));
  assert property (!aresetn |-> (m_axis_tvalid == 1'b0 && m_axis_tlast == 1'b0));

  // Combinational definitions
  assert property (int_comp_wire   == (int_cntr_reg < cfg_data));
  assert property (int_tvalid_wire == (int_enbl_reg & s_axis_tvalid));
  assert property (int_tlast_wire  == ~int_comp_wire);

  // Output mappings
  assert property (m_axis_tvalid == int_tvalid_wire);
  assert property (m_axis_tlast  == (int_enbl_reg & int_tlast_wire));
  assert property (m_axis_tdata  == s_axis_tdata);

  // Ready mapping
  generate
    if (ALWAYS_READY == "TRUE") begin
      assert property (s_axis_tready == 1'b1);
    end else begin
      assert property (s_axis_tready == (int_enbl_reg & m_axis_tready));
    end
  endgenerate

  // Enable behavior
  assert property ((~int_enbl_reg & int_comp_wire) |=> int_enbl_reg); // start when comp true
  generate
    if (CONTINUOUS == "TRUE") begin
      // Never falls (except during reset)
      assert property (!$fell(int_enbl_reg));
    end else begin
      // STOP: disable on last handshake
      assert property ((m_axis_tready & int_tvalid_wire & int_tlast_wire) |=> !int_enbl_reg);
    end
  endgenerate

  // Counter behavior
  // Increment only on handshake while comp true
  assert property ((m_axis_tready & int_tvalid_wire & int_comp_wire) |=> int_cntr_reg == $past(int_cntr_reg)+1);
  // No increment when no handshake
  assert property (!(m_axis_tready & int_tvalid_wire) |=> $stable(int_cntr_reg));
  // No increment when comp false
  assert property ((m_axis_tready & int_tvalid_wire & !int_comp_wire) |=> int_cntr_reg == $past(int_cntr_reg));
  // Mode-specific last handling
  generate
    if (CONTINUOUS == "TRUE") begin
      // On last handshake, counter resets next cycle, enable stays set
      assert property ((m_axis_tready & int_tvalid_wire & int_tlast_wire) |=> (int_cntr_reg == '0 && int_enbl_reg));
    end else begin
      // On last handshake, counter holds, enable clears
      assert property ((m_axis_tready & int_tvalid_wire & int_tlast_wire) |=> ($stable(int_cntr_reg) && !int_enbl_reg));
    end
  endgenerate

  // TLAST correctness
  assert property (m_axis_tlast |-> m_axis_tvalid); // AXIS rule: TLAST implies TVALID
  assert property (m_axis_tlast |-> (int_cntr_reg >= cfg_data));
  assert property ((m_axis_tvalid & m_axis_tready & m_axis_tlast) |-> (int_cntr_reg == cfg_data));

  // Packet length monotonicity (no TLAST while comp true)
  assert property (int_comp_wire |-> !m_axis_tlast);

  // Key coverage
  cover property ($rose(int_enbl_reg));
  cover property (m_axis_tvalid & m_axis_tready & !m_axis_tlast); // mid-packet beat
  cover property (m_axis_tvalid & m_axis_tready & m_axis_tlast);  // last beat
  generate
    if (CONTINUOUS == "TRUE") begin
      cover property ((m_axis_tvalid & m_axis_tready & m_axis_tlast) ##1 (int_cntr_reg == '0 && int_enbl_reg)); // wrap
    end else begin
      cover property ((m_axis_tvalid & m_axis_tready & m_axis_tlast) ##1 (!int_enbl_reg)); // stop after last
    end
  endgenerate
endmodule