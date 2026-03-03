// SVA for sky130_fd_sc_hd__fa (full adder)
// Bind this file to the DUT: bind sky130_fd_sc_hd__fa sky130_fd_sc_hd__fa_sva sva (.*);

module sky130_fd_sc_hd__fa_sva (
  input logic A,
  input logic B,
  input logic CIN,
  input logic VPWR,
  input logic VGND,
  input logic VPB,
  input logic VNB,
  input logic COUT,
  input logic SUM
);

  // Power/validity guards
  wire power_good   = (VPWR === 1'b1) && (VGND === 1'b0) && (VPB === 1'b1) && (VNB === 1'b0);
  wire inputs_known = !$isunknown({A,B,CIN});

  // Functional correctness, zero-delay (same-timestep) response on any input/power change
  property p_fulladder_func;
    @(A or B or CIN or VPWR or VGND or VPB or VNB)
      disable iff (!(power_good && inputs_known))
        1'b1 |-> ##0 (
          // Sum and Carry correctness (also enforces outputs not X/Z)
          (SUM  === (A ^ B ^ CIN)) &&
          (COUT === ((A & B) | (A & CIN) | (B & CIN)))
        );
  endproperty
  assert property (p_fulladder_func);

  // Propagate condition: when A^B=1, carry propagates and sum inverts CIN
  property p_propagate;
    @(A or B or CIN)
      disable iff (!(power_good && inputs_known))
        (A ^ B) |-> ##0 ((COUT === CIN) && (SUM === ~CIN));
  endproperty
  assert property (p_propagate);

  // Generate condition: when A&B=1, carry is 1; sum equals CIN
  property p_generate;
    @(A or B or CIN)
      disable iff (!(power_good && inputs_known))
        (A & B) |-> ##0 ((COUT === 1'b1) && (SUM === CIN));
  endproperty
  assert property (p_generate);

  // Kill condition: when A|B=0, carry is 0; sum equals CIN
  property p_kill;
    @(A or B or CIN)
      disable iff (!(power_good && inputs_known))
        (~(A | B)) |-> ##0 ((COUT === 1'b0) && (SUM === CIN));
  endproperty
  assert property (p_kill);

  // Full truth-table coverage (under valid power and known inputs), with expected outputs
  cover property (@(A or B or CIN or VPWR or VGND or VPB or VNB)
    power_good && inputs_known && (A===1'b0) && (B===1'b0) && (CIN===1'b0) && (SUM===1'b0) && (COUT===1'b0));
  cover property (@(A or B or CIN or VPWR or VGND or VPB or VNB)
    power_good && inputs_known && (A===1'b0) && (B===1'b0) && (CIN===1'b1) && (SUM===1'b1) && (COUT===1'b0));
  cover property (@(A or B or CIN or VPWR or VGND or VPB or VNB)
    power_good && inputs_known && (A===1'b0) && (B===1'b1) && (CIN===1'b0) && (SUM===1'b1) && (COUT===1'b0));
  cover property (@(A or B or CIN or VPWR or VGND or VPB or VNB)
    power_good && inputs_known && (A===1'b0) && (B===1'b1) && (CIN===1'b1) && (SUM===1'b0) && (COUT===1'b1));
  cover property (@(A or B or CIN or VPWR or VGND or VPB or VNB)
    power_good && inputs_known && (A===1'b1) && (B===1'b0) && (CIN===1'b0) && (SUM===1'b1) && (COUT===1'b0));
  cover property (@(A or B or CIN or VPWR or VGND or VPB or VNB)
    power_good && inputs_known && (A===1'b1) && (B===1'b0) && (CIN===1'b1) && (SUM===1'b0) && (COUT===1'b1));
  cover property (@(A or B or CIN or VPWR or VGND or VPB or VNB)
    power_good && inputs_known && (A===1'b1) && (B===1'b1) && (CIN===1'b0) && (SUM===1'b0) && (COUT===1'b1));
  cover property (@(A or B or CIN or VPWR or VGND or VPB or VNB)
    power_good && inputs_known && (A===1'b1) && (B===1'b1) && (CIN===1'b1) && (SUM===1'b1) && (COUT===1'b1));

endmodule

// Bind example (place in a separate file or below):
// bind sky130_fd_sc_hd__fa sky130_fd_sc_hd__fa_sva sva (.*);