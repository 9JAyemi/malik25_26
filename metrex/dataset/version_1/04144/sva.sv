// SVA for axis_phase_generator
// Bind-friendly: references internal regs via ports

module axis_phase_generator_sva #(
  parameter int AXIS_TDATA_WIDTH = 32,
  parameter int PHASE_WIDTH      = 30
)(
  input  logic                        aclk,
  input  logic                        aresetn,
  input  logic [PHASE_WIDTH-1:0]      cfg_data,
  input  logic                        m_axis_tready,
  input  logic [AXIS_TDATA_WIDTH-1:0] m_axis_tdata,
  input  logic                        m_axis_tvalid,
  input  logic [PHASE_WIDTH-1:0]      int_cntr_reg,
  input  logic                        int_enbl_reg
);

  // Sanity on parameters
  initial begin
    assert (AXIS_TDATA_WIDTH >= PHASE_WIDTH)
      else $error("AXIS_TDATA_WIDTH (%0d) must be >= PHASE_WIDTH (%0d)", AXIS_TDATA_WIDTH, PHASE_WIDTH);
  end

  // Past-valid guard for $past
  logic past_valid;
  always_ff @(posedge aclk) begin
    if (!aresetn) past_valid <= 1'b0;
    else          past_valid <= 1'b1;
  end

  // Default clocking
  default clocking cb @(posedge aclk); endclocking

  // Reset state checks (not disabled during reset)
  assert property (@cb !aresetn |-> (int_enbl_reg==1'b0 && int_cntr_reg=='0 &&
                                     m_axis_tvalid==1'b0 && m_axis_tdata=='0))
    else $error("Reset state mismatch");

  // Operational checks
  default disable iff (!aresetn)

  // Valid reflects enable exactly
  assert property (@cb m_axis_tvalid == int_enbl_reg)
    else $error("m_axis_tvalid must mirror int_enbl_reg");

  // Enable asserts immediately after reset and sticks high thereafter
  assert property (@cb $rose(aresetn) |-> m_axis_tvalid)
    else $error("m_axis_tvalid must assert right after reset release");
  assert property (@cb m_axis_tvalid |=> m_axis_tvalid)
    else $error("m_axis_tvalid must not deassert while out of reset");

  // Counter update semantics
  assert property (@cb past_valid && (int_enbl_reg && m_axis_tready)
                   |=> int_cntr_reg == $past(int_cntr_reg) + cfg_data)
    else $error("Counter must increment by cfg_data on ready when enabled");

  assert property (@cb past_valid && (!int_enbl_reg || !m_axis_tready)
                   |=> int_cntr_reg == $past(int_cntr_reg))
    else $error("Counter must hold when not enabled or not ready");

  // First valid cycle data must be zero (counter not yet incremented)
  assert property (@cb past_valid && ! $past(m_axis_tvalid) && m_axis_tvalid
                   |-> (int_cntr_reg=='0 && m_axis_tdata=='0))
    else $error("First valid cycle must present zero data");

  // Data mapping: sign-extend counter into TDATA
  assert property (@cb m_axis_tdata[PHASE_WIDTH-1:0] == int_cntr_reg)
    else $error("TDATA low bits must equal counter");
  if (AXIS_TDATA_WIDTH > PHASE_WIDTH) begin
    assert property (@cb m_axis_tdata[AXIS_TDATA_WIDTH-1:PHASE_WIDTH]
                     == { (AXIS_TDATA_WIDTH-PHASE_WIDTH) { int_cntr_reg[PHASE_WIDTH-1] } })
      else $error("TDATA upper bits must sign-extend counter MSB");
  end

  // No X/Z on outputs when out of reset
  assert property (@cb !$isunknown({m_axis_tvalid, m_axis_tdata}))
    else $error("Outputs contain X/Z when out of reset");

  // Functional coverage
  cover property (@cb $rose(aresetn) ##1 m_axis_tvalid);
  cover property (@cb int_enbl_reg && m_axis_tready); // increment opportunity
  cover property (@cb past_valid && int_enbl_reg && m_axis_tready && cfg_data!='0
                   ##1 (int_cntr_reg < $past(int_cntr_reg))); // wrap-around
  cover property (@cb int_cntr_reg[PHASE_WIDTH-1]); // negative/sign-ext case observed

endmodule

// Bind into DUT (example):
// bind axis_phase_generator axis_phase_generator_sva #(
//   .AXIS_TDATA_WIDTH(AXIS_TDATA_WIDTH),
//   .PHASE_WIDTH(PHASE_WIDTH)
// ) axis_phase_generator_sva_i (.*);