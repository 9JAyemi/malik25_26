// SVA checker for db_lut_tc
// Concise, high-quality assertions + coverage; bindable, no DUT changes

module db_lut_tc_sva (
  input  logic [5:0] qp_i,
  input  logic       mb_type_i,
  input  logic [4:0] tc_o
);
  timeunit 1ns; timeprecision 1ps;

  // Derived inputs
  logic [5:0] qp_w_ref;
  assign qp_w_ref = qp_i + {mb_type_i,1'b0};

  // Sampling pulse for a clockless DUT
  logic mon_clk /* synthesis keep */;
  initial mon_clk = 0;
  always @(qp_i or mb_type_i or tc_o) mon_clk <= ~mon_clk;

  // Golden reference for tc
  function automatic logic [4:0] tc_ref (input logic [5:0] qpw);
    case (qpw)
      6'd18,6'd19,6'd20,6'd21,6'd22,6'd23,6'd24,6'd25,6'd26:  tc_ref = 5'd1;
      6'd27,6'd28,6'd29,6'd30:                                tc_ref = 5'd2;
      6'd31,6'd32,6'd33,6'd34:                                tc_ref = 5'd3;
      6'd35,6'd36,6'd37:                                      tc_ref = 5'd4;
      6'd38,6'd39:                                            tc_ref = 5'd5;
      6'd40,6'd41:                                            tc_ref = 5'd6;
      6'd42:                                                  tc_ref = 5'd7;
      6'd43:                                                  tc_ref = 5'd8;
      6'd44:                                                  tc_ref = 5'd9;
      6'd45:                                                  tc_ref = 5'd10;
      6'd46:                                                  tc_ref = 5'd11;
      6'd47:                                                  tc_ref = 5'd13;
      6'd48:                                                  tc_ref = 5'd14;
      6'd49:                                                  tc_ref = 5'd16;
      6'd50:                                                  tc_ref = 5'd18;
      6'd51:                                                  tc_ref = 5'd20;
      6'd52:                                                  tc_ref = 5'd22;
      6'd53:                                                  tc_ref = 5'd24;
      default:                                                tc_ref = 5'd0;
    endcase
  endfunction

  // No X on output when inputs are known
  property p_no_x_on_known_inputs;
    !$isunknown({qp_i,mb_type_i}) |-> !$isunknown(tc_o);
  endproperty
  assert property (@(posedge mon_clk) p_no_x_on_known_inputs)
    else $error("tc_o is X/Z when inputs are known");

  // Output is exactly the table (golden reference)
  property p_exact_lookup;
    disable iff ($isunknown({qp_i,mb_type_i,tc_o}))
      tc_o == tc_ref(qp_w_ref);
  endproperty
  assert property (@(posedge mon_clk) p_exact_lookup)
    else $error("tc_o (%0d) != tc_ref(%0d)", tc_o, qp_w_ref);

  // Output range safety
  property p_range_safety;
    disable iff ($isunknown({qp_i,mb_type_i,tc_o}))
      tc_o inside {[5'd0:5'd24]};
  endproperty
  assert property (@(posedge mon_clk) p_range_safety)
    else $error("tc_o out of expected range 0..24: %0d", tc_o);

  // Default case explicitly 0 outside 18..53
  property p_default_zero;
    disable iff ($isunknown({qp_i,mb_type_i,tc_o}))
      (qp_w_ref < 6'd18 || qp_w_ref > 6'd53) |-> (tc_o == 5'd0);
  endproperty
  assert property (@(posedge mon_clk) p_default_zero)
    else $error("Default case violated: qp_w_ref=%0d tc_o=%0d", qp_w_ref, tc_o);

  // Glitch-free: if inputs didn't change, output must not change
  property p_no_glitch_when_inputs_stable;
    !$changed({qp_i,mb_type_i}) |-> !$changed(tc_o);
  endproperty
  assert property (@(posedge mon_clk) p_no_glitch_when_inputs_stable)
    else $error("tc_o changed without input change");

  // Coverage: every table entry, boundaries, and modes
  // All mapped values exercised with correct output
  genvar v;
  generate
    for (v = 18; v <= 53; v++) begin : GEN_CVR_TABLE
      cover property (@(posedge mon_clk)
        !$isunknown({qp_i,mb_type_i}) &&
        (qp_w_ref == v) && (tc_o == tc_ref(v))
      );
    end
  endgenerate

  // Boundary covers
  cover property (@(posedge mon_clk) !$isunknown({qp_i,mb_type_i}) && qp_w_ref == 6'd17 && tc_o == 5'd0);
  cover property (@(posedge mon_clk) !$isunknown({qp_i,mb_type_i}) && qp_w_ref == 6'd18 && tc_o == tc_ref(6'd18));
  cover property (@(posedge mon_clk) !$isunknown({qp_i,mb_type_i}) && qp_w_ref == 6'd53 && tc_o == tc_ref(6'd53));
  cover property (@(posedge mon_clk) !$isunknown({qp_i,mb_type_i}) && qp_w_ref == 6'd54 && tc_o == 5'd0);

  // Mode covers (mb_type_i both values)
  cover property (@(posedge mon_clk) mb_type_i == 1'b0);
  cover property (@(posedge mon_clk) mb_type_i == 1'b1);

  // Overflow/wrap scenarios when adding 2
  cover property (@(posedge mon_clk) mb_type_i && (qp_i >= 6'd62)); // wrap potential
endmodule

// Bind into DUT
bind db_lut_tc db_lut_tc_sva db_lut_tc_sva_i (
  .qp_i(qp_i),
  .mb_type_i(mb_type_i),
  .tc_o(tc_o)
);