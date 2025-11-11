// SystemVerilog Assertions for RegFile
// Bind into DUT scope; no TB code required.

module RegFile_sva;
  // Use DUT scope signals directly (bind into RegFile)
  // clk, RegWrite, regA, regB, regTEST, regW, Wdat, Adat, Bdat, TESTdat, regfile

  default clocking cb @(posedge clk); endclocking

  // Guard first-cycle $past usage
  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Combinational read correctness (sampled each clk)
  assert property (Adat    == regfile[regA]);
  assert property (Bdat    == regfile[regB]);
  assert property (TESTdat == regfile[regTEST]);

  // Write behavior (observable next cycle due to sampling semantics)
  // - Write to non-zero register updates with Wdat
  // - Write to x0 forces zero
  assert property (RegWrite && (regW != 5'd0) |=> regfile[regW] == $past(Wdat));
  assert property (RegWrite && (regW == 5'd0) |=> regfile[5'd0] == 32'h0);

  // RAW visibility on read ports (next-cycle)
  assert property (RegWrite && (regW != 5'd0) && (regA == regW) |=> Adat    == $past(Wdat));
  assert property (RegWrite && (regW != 5'd0) && (regB == regW) |=> Bdat    == $past(Wdat));
  assert property (RegWrite && (regW != 5'd0) && (regTEST == regW) |=> TESTdat == $past(Wdat));

  // After writing x0, reads of x0 return zero (next-cycle)
  assert property (RegWrite && (regW == 5'd0) && (regA == 5'd0) |=> Adat    == 32'h0);
  assert property (RegWrite && (regW == 5'd0) && (regB == 5'd0) |=> Bdat    == 32'h0);
  assert property (RegWrite && (regW == 5'd0) && (regTEST == 5'd0) |=> TESTdat == 32'h0);

  // No unintended writes:
  // - When RegWrite==0, no register changes at this edge
  // - When writing, only the targeted entry may change
  genvar i;
  generate
    for (i = 0; i < 32; i++) begin : g_nounint
      assert property (!RegWrite |-> regfile[i] == $past(regfile[i]));
      assert property (RegWrite && (regW != i) |=> regfile[i] == $past(regfile[i]));
      if (i != 0) begin
        assert property (RegWrite && (regW == i) |=> regfile[i] == $past(Wdat));
      end else begin
        assert property (RegWrite && (regW == 0) |=> regfile[0] == 32'h0);
      end
    end
  endgenerate

  // Functional coverage
  cover property (RegWrite && (regW != 5'd0));
  cover property (RegWrite && (regW == 5'd0));
  cover property (RegWrite && (regW != 5'd0) && (regA == regW));
  cover property (RegWrite && (regW != 5'd0) && (regB == regW));
  cover property (RegWrite && (regW != 5'd0) && (regTEST == regW));
  cover property (!RegWrite);

endmodule

// Bind to all RegFile instances
bind RegFile RegFile_sva rf_sva();