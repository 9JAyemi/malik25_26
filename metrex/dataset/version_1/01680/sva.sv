// SVA for mux4to1. Bind into DUT; focuses on correctness and essential coverage.

module mux4to1_sva (mux4to1 dut);

  // Combinational equivalence and internal inversions
  always_comb begin
    assert (dut.notS0 === ~dut.S[0]) else $error("mux4to1: notS0 != ~S[0]");
    assert (dut.notS1 === ~dut.S[1]) else $error("mux4to1: notS1 != ~S[1]");
    assert (dut.Y === ((dut.A & dut.notS1 & dut.notS0) |
                       (dut.B & dut.notS1 & dut.S[0]) |
                       (dut.C & dut.S[1] & dut.notS0) |
                       (dut.D & dut.S[1] & dut.S[0])))
      else $error("mux4to1: Y != combinational function");
  end

  // Selected mapping must hold on any relevant edge (guard X on S)
  property mux_select_map;
    @(posedge dut.A or negedge dut.A or
      posedge dut.B or negedge dut.B or
      posedge dut.C or negedge dut.C or
      posedge dut.D or negedge dut.D or
      posedge dut.S[0] or negedge dut.S[0] or
      posedge dut.S[1] or negedge dut.S[1])
    disable iff ($isunknown(dut.S))
      1'b1 |-> (
        ((dut.S==2'b00) ? (dut.Y === dut.A) : 1'b1) &&
        ((dut.S==2'b01) ? (dut.Y === dut.B) : 1'b1) &&
        ((dut.S==2'b10) ? (dut.Y === dut.C) : 1'b1) &&
        ((dut.S==2'b11) ? (dut.Y === dut.D) : 1'b1)
      );
  endproperty
  assert property (mux_select_map);

  // Output follows selected input edges
  property follow_A; @(posedge dut.A or negedge dut.A) disable iff ($isunknown(dut.S)) (dut.S==2'b00) |-> (dut.Y === dut.A); endproperty
  property follow_B; @(posedge dut.B or negedge dut.B) disable iff ($isunknown(dut.S)) (dut.S==2'b01) |-> (dut.Y === dut.B); endproperty
  property follow_C; @(posedge dut.C or negedge dut.C) disable iff ($isunknown(dut.S)) (dut.S==2'b10) |-> (dut.Y === dut.C); endproperty
  property follow_D; @(posedge dut.D or negedge dut.D) disable iff ($isunknown(dut.S)) (dut.S==2'b11) |-> (dut.Y === dut.D); endproperty
  assert property (follow_A);
  assert property (follow_B);
  assert property (follow_C);
  assert property (follow_D);

  // Coverage: each select value observed
  cover property (@(posedge dut.S[0] or negedge dut.S[0] or posedge dut.S[1] or negedge dut.S[1]) dut.S==2'b00);
  cover property (@(posedge dut.S[0] or negedge dut.S[0] or posedge dut.S[1] or negedge dut.S[1]) dut.S==2'b01);
  cover property (@(posedge dut.S[0] or negedge dut.S[0] or posedge dut.S[1] or negedge dut.S[1]) dut.S==2'b10);
  cover property (@(posedge dut.S[0] or negedge dut.S[0] or posedge dut.S[1] or negedge dut.S[1]) dut.S==2'b11);

  // Coverage: rising/falling of selected input propagates to Y
  cover property (@(posedge dut.A) (dut.S==2'b00 && dut.Y===1'b1));
  cover property (@(posedge dut.B) (dut.S==2'b01 && dut.Y===1'b1));
  cover property (@(posedge dut.C) (dut.S==2'b10 && dut.Y===1'b1));
  cover property (@(posedge dut.D) (dut.S==2'b11 && dut.Y===1'b1));
  cover property (@(negedge dut.A) (dut.S==2'b00 && dut.Y===1'b0));
  cover property (@(negedge dut.B) (dut.S==2'b01 && dut.Y===1'b0));
  cover property (@(negedge dut.C) (dut.S==2'b10 && dut.Y===1'b0));
  cover property (@(negedge dut.D) (dut.S==2'b11 && dut.Y===1'b0));

endmodule

bind mux4to1 mux4to1_sva sva_inst();