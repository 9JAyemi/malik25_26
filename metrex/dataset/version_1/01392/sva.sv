// SVA for RegGPR: concise, high-quality checks and coverage (bindable checker).
// Focus: decode correctness, bank selection, read/write behavior, and essential coverage.

module RegGPR_sva(
  input  logic        clock,
  input  logic        reset,
  input  logic [6:0]  regIdRs, regIdRt, regIdRm, regIdRn,
  input  logic [31:0] regValRn,
  input  logic [31:0] regSrVal,
  input  logic [31:0] regValRs, regValRt, regValRm
);

  // Local abstract model of register banks to predict reads (no access to DUT internals needed)
  logic [31:0] la[8], lb[8], h[8];
  bit          vla[8], vlb[8], vh[8];

  // Init valid masks
  initial begin
    foreach (vla[i]) vla[i] = 0;
    foreach (vlb[i]) vlb[i] = 0;
    foreach (vh[i])  vh[i]  = 0;
  end

  // Model writes (matches DUT)
  always_ff @(posedge clock) begin
    automatic bit rb = regSrVal[29];
    automatic logic [2:0] i = regIdRn[2:0];
    unique case (regIdRn[6:3])
      4'h0: begin
        if (rb) begin lb[i] <= regValRn; vlb[i] <= 1; end
        else    begin la[i] <= regValRn; vla[i] <= 1; end
      end
      4'h1: begin h[i] <= regValRn; vh[i] <= 1; end
      4'h4: begin // inverted mapping vs group 0
        if (rb) begin la[i] <= regValRn; vla[i] <= 1; end
        else    begin lb[i] <= regValRn; vlb[i] <= 1; end
      end
      default: /* no-op */;
    endcase
  end

  // Basic X-safety on control fields
  assert property (@(posedge clock) !$isunknown({regIdRs[6:3],regIdRt[6:3],regIdRm[6:3],regIdRn[6:3],regSrVal[29]}));
  assert property (@(negedge clock) !$isunknown({regIdRs[6:3],regIdRt[6:3],regIdRm[6:3],regIdRn[6:3],regSrVal[29]}));

  // Helper macros for concise assertions
  `define A_RD_ZERO_OTHERS(portId,portVal) \
    assert property (@(posedge clock) ((portId[6:3] != 4'h0) && (portId[6:3] != 4'h1) && (portId[6:3] != 4'h4)) |-> (portVal == 32'h0)); \
    assert property (@(negedge clock) ((portId[6:3] != 4'h0) && (portId[6:3] != 4'h1) && (portId[6:3] != 4'h4)) |-> (portVal == 32'h0));

  `define A_RD_G1(portId,portVal) \
    assert property (@(posedge clock) ((portId[6:3] == 4'h1) && vh[portId[2:0]]) |-> (portVal == h[portId[2:0]])); \
    assert property (@(negedge clock) ((portId[6:3] == 4'h1) && vh[portId[2:0]]) |-> (portVal == h[portId[2:0]]));

  `define A_RD_G0_G4(portId,portVal) \
    assert property (@(posedge clock) ((portId[6:3] inside {4'h0,4'h4}) && (regSrVal[29] ? vlb[portId[2:0]] : vla[portId[2:0]])) \
                     |-> (portVal == (regSrVal[29] ? lb[portId[2:0]] : la[portId[2:0]]))); \
    assert property (@(negedge clock) ((portId[6:3] inside {4'h0,4'h4}) && (regSrVal[29] ? vlb[portId[2:0]] : vla[portId[2:0]])) \
                     |-> (portVal == (regSrVal[29] ? lb[portId[2:0]] : la[portId[2:0]])));

  // Read mux correctness for all three read ports, at both edges
  `A_RD_ZERO_OTHERS(regIdRs, regValRs)
  `A_RD_ZERO_OTHERS(regIdRt, regValRt)
  `A_RD_ZERO_OTHERS(regIdRm, regValRm)

  `A_RD_G1(regIdRs, regValRs)
  `A_RD_G1(regIdRt, regValRt)
  `A_RD_G1(regIdRm, regValRm)

  `A_RD_G0_G4(regIdRs, regValRs)
  `A_RD_G0_G4(regIdRt, regValRt)
  `A_RD_G0_G4(regIdRm, regValRm)

  // Write decode assertions (structural correctness of group selection and inversion)
  // Group-0 writes go to bank selected by RB at posedge
  assert property (@(posedge clock)
    (regIdRn[6:3] == 4'h0 && regSrVal[29] == 1'b0) |-> (vla[regIdRn[2:0]] && la[regIdRn[2:0]] == $past(regValRn)));
  assert property (@(posedge clock)
    (regIdRn[6:3] == 4'h0 && regSrVal[29] == 1'b1) |-> (vlb[regIdRn[2:0]] && lb[regIdRn[2:0]] == $past(regValRn)));

  // Group-1 writes go to H bank
  assert property (@(posedge clock)
    (regIdRn[6:3] == 4'h1) |-> (vh[regIdRn[2:0]] && h[regIdRn[2:0]] == $past(regValRn)));

  // Group-4 writes go to the inverted bank (vs RB)
  assert property (@(posedge clock)
    (regIdRn[6:3] == 4'h4 && regSrVal[29] == 1'b0) |-> (vlb[regIdRn[2:0]] && lb[regIdRn[2:0]] == $past(regValRn)));
  assert property (@(posedge clock)
    (regIdRn[6:3] == 4'h4 && regSrVal[29] == 1'b1) |-> (vla[regIdRn[2:0]] && la[regIdRn[2:0]] == $past(regValRn)));

  // Minimal, meaningful coverage
  // 1) Exercise all write paths (G0/G1/G4) under both RB values
  cover property (@(posedge clock) regIdRn[6:3]==4'h0 && regSrVal[29]==1'b0);
  cover property (@(posedge clock) regIdRn[6:3]==4'h0 && regSrVal[29]==1'b1);
  cover property (@(posedge clock) regIdRn[6:3]==4'h1);
  cover property (@(posedge clock) regIdRn[6:3]==4'h4 && regSrVal[29]==1'b0);
  cover property (@(posedge clock) regIdRn[6:3]==4'h4 && regSrVal[29]==1'b1);

  // 2) Exercise read ports selecting each bank/H
  cover property (@(posedge clock) regIdRs[6:3]==4'h1);
  cover property (@(posedge clock) regIdRt[6:3]==4'h1);
  cover property (@(posedge clock) regIdRm[6:3]==4'h1);
  cover property (@(posedge clock) regIdRs[6:3] inside {4'h0,4'h4} && regSrVal[29]==1'b0);
  cover property (@(posedge clock) regIdRs[6:3] inside {4'h0,4'h4} && regSrVal[29]==1'b1);

  // 3) Read-after-write visibility at next edge(s)
  // Same RB for G0/G1 paths: value visible at next posedge if address matches
  cover property (@(posedge clock)
    (regIdRn[6:3] inside {4'h0,4'h1} && regSrVal[29]==$past(regSrVal[29])) ##1
    ((regIdRs[6:3] inside {4'h0,4'h1,4'h4}) && regIdRs[2:0]==$past(regIdRn[2:0]) && regValRs==$past(regValRn)));

  // G4 inverted mapping requires RB flip between write and read (to select written bank)
  cover property (@(posedge clock)
    (regIdRn[6:3]==4'h4 && regSrVal[29]==1'b0) ##1
    (regSrVal[29]==1'b1 && regIdRs[6:3]==4'h4 && regIdRs[2:0]==$past(regIdRn[2:0]) && regValRs==$past(regValRn)));
  cover property (@(posedge clock)
    (regIdRn[6:3]==4'h4 && regSrVal[29]==1'b1) ##1
    (regSrVal[29]==1'b0 && regIdRs[6:3]==4'h4 && regIdRs[2:0]==$past(regIdRn[2:0]) && regValRs==$past(regValRn)));

endmodule

// Bind this checker to the DUT
bind RegGPR RegGPR_sva u_RegGPR_sva (
  .clock   (clock),
  .reset   (reset),
  .regIdRs (regIdRs),
  .regIdRt (regIdRt),
  .regIdRm (regIdRm),
  .regIdRn (regIdRn),
  .regValRn(regValRn),
  .regSrVal(regSrVal),
  .regValRs(regValRs),
  .regValRt(regValRt),
  .regValRm(regValRm)
);