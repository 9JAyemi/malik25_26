// SVA checker for mux8to1
module mux8to1_sva (
  input logic y,
  input logic s2, s1, s0,
  input logic d4, d3, d2, d1, d0
);

  logic [2:0] sel = {s2,s1,s0};
  logic expected_y;
  assign expected_y = (sel==3'b000) ? d0 :
                      (sel==3'b001) ? d1 :
                      (sel==3'b010) ? d2 :
                      (sel==3'b011) ? d3 :
                      (sel==3'b100) ? d4 : 1'b0;

  // Functional equivalence on any relevant change
  property p_func;
    @(s0 or s1 or s2 or d0 or d1 or d2 or d3 or d4 or y) (y === expected_y);
  endproperty
  assert property (p_func)
    else $error("mux8to1: y mismatch sel=%b d={%b%b%b%b%b} y=%b exp=%b", sel,d4,d3,d2,d1,d0,y,expected_y);

  // If sel and selected input are known, y must be known
  function automatic logic selected_known;
    case (sel)
      3'b000: selected_known = !$isunknown(d0);
      3'b001: selected_known = !$isunknown(d1);
      3'b010: selected_known = !$isunknown(d2);
      3'b011: selected_known = !$isunknown(d3);
      3'b100: selected_known = !$isunknown(d4);
      default: selected_known = 1'b1; // default path is constant 0
    endcase
  endfunction

  property p_no_x_when_known;
    @(s0 or s1 or s2 or d0 or d1 or d2 or d3 or d4)
      (!$isunknown(sel) && selected_known()) |-> !$isunknown(y);
  endproperty
  assert property (p_no_x_when_known)
    else $error("mux8to1: y is X/Z while inputs select a known value");

  // Default path must drive 0
  property p_default_zero;
    @(s0 or s1 or s2) (sel inside {3'b101,3'b110,3'b111}) |-> (y === 1'b0);
  endproperty
  assert property (p_default_zero)
    else $error("mux8to1: default select should force y=0");

  // Coverage: hit all select values
  cover property (@(s0 or s1 or s2) sel==3'b000);
  cover property (@(s0 or s1 or s2) sel==3'b001);
  cover property (@(s0 or s1 or s2) sel==3'b010);
  cover property (@(s0 or s1 or s2) sel==3'b011);
  cover property (@(s0 or s1 or s2) sel==3'b100);
  cover property (@(s0 or s1 or s2) sel==3'b101);
  cover property (@(s0 or s1 or s2) sel==3'b110);
  cover property (@(s0 or s1 or s2) sel==3'b111);

  // Coverage: each data selection drives y; default drives 0
  cover property (@(s0 or s1 or s2 or d0) (sel==3'b000) && (y===d0));
  cover property (@(s0 or s1 or s2 or d1) (sel==3'b001) && (y===d1));
  cover property (@(s0 or s1 or s2 or d2) (sel==3'b010) && (y===d2));
  cover property (@(s0 or s1 or s2 or d3) (sel==3'b011) && (y===d3));
  cover property (@(s0 or s1 or s2 or d4) (sel==3'b100) && (y===d4));
  cover property (@(s0 or s1 or s2)       (sel inside {3'b101,3'b110,3'b111}) && (y===1'b0));

endmodule

// Bind into the DUT
bind mux8to1 mux8to1_sva u_mux8to1_sva(.*);