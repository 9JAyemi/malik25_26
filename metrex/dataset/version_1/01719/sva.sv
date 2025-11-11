// SVA for mux_2to1
module mux_2to1_sva (
  input logic [1:0] data_in,
  input logic       sel,
  input logic       data_out
);
  // Clockless assertions/coverage over combinational activity
  default clocking cb @(*); endclocking

  // Functional equivalence (golden reference)
  a_func_eq: assert property (data_out === (sel ? data_in[1] : data_in[0]))
    else $error("mux_2to1: data_out != selected input");

  // Masking: changes on unselected input must not affect output (allow 0-delay settle)
  a_mask1: assert property ((sel==1'b0 && $changed(data_in[1])) |-> ##0 $stable(data_out))
    else $error("mux_2to1: unselected data_in[1] affected data_out when sel=0");
  a_mask0: assert property ((sel==1'b1 && $changed(data_in[0])) |-> ##0 $stable(data_out))
    else $error("mux_2to1: unselected data_in[0] affected data_out when sel=1");

  // Selected path follows (allow 0-delay settle)
  a_follow0: assert property ((sel==1'b0 && $changed(data_in[0])) |-> ##0 (data_out === data_in[0]))
    else $error("mux_2to1: data_out did not follow data_in[0] when sel=0");
  a_follow1: assert property ((sel==1'b1 && $changed(data_in[1])) |-> ##0 (data_out === data_in[1]))
    else $error("mux_2to1: data_out did not follow data_in[1] when sel=1");

  // No glitch on sel toggle if both inputs equal and known
  a_noglitch_sel_eq: assert property (
    (($rose(sel) || $fell(sel)) && (data_in[0] === data_in[1]) && !$isunknown(data_in[0]))
      |-> ##0 ($stable(data_out) && data_out === data_in[0])
  ) else $error("mux_2to1: data_out glitched on sel toggle with equal inputs");

  // X-propagation semantics
  a_x_sel_x_unequal: assert property (($isunknown(sel) && (data_in[0] !== data_in[1])) |-> $isunknown(data_out))
    else $error("mux_2to1: expected X on data_out when sel is X and inputs differ");
  a_x_sel_x_equal: assert property (($isunknown(sel) && (data_in[0] === data_in[1])) |-> (data_out === data_in[0]))
    else $error("mux_2to1: expected resolved value when sel is X and inputs equal");
  a_x_selected: assert property (
    ((sel==1'b0) && $isunknown(data_in[0])) |-> $isunknown(data_out)
  ) else $error("mux_2to1: expected X on data_out when sel=0 and data_in[0] is X");
  a_x_selected2: assert property (
    ((sel==1'b1) && $isunknown(data_in[1])) |-> $isunknown(data_out)
  ) else $error("mux_2to1: expected X on data_out when sel=1 and data_in[1] is X");

  // Coverage
  c_sel_rise:   cover property ($rose(sel));
  c_sel_fall:   cover property ($fell(sel));
  c_patterns0:  cover property (data_in==2'b00);
  c_patterns1:  cover property (data_in==2'b01);
  c_patterns2:  cover property (data_in==2'b10);
  c_patterns3:  cover property (data_in==2'b11);
  c_path0_follow: cover property ((sel==0 && $changed(data_in[0])) ##0 (data_out===data_in[0]));
  c_path1_follow: cover property ((sel==1 && $changed(data_in[1])) ##0 (data_out===data_in[1]));
  c_x_sel_diff: cover property ($isunknown(sel) && (data_in[0] !== data_in[1]) && $isunknown(data_out));
  c_x_sel_eq:   cover property ($isunknown(sel) && (data_in[0] === data_in[1]) && (data_out===data_in[0]));
endmodule

// Bind into DUT
bind mux_2to1 mux_2to1_sva sva_mux_2to1 (.data_in(data_in), .sel(sel), .data_out(data_out));