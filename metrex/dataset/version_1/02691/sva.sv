// SVA bind file for MUX_4to1
module MUX_4to1_sva (
  input  logic in0, in1, in2, in3,
  input  logic sel,
  input  logic en,
  input  logic out,
  input  logic selected
);

  // Compile-time sanity: sel must be 2 bits (will flag current DUT bug)
  initial assert ($bits(sel) == 2)
    else $error("MUX_4to1 sel width is %0d, expected 2", $bits(sel));

  // Functional equivalence (sample after delta to avoid race)
  property p_func;
    @(in0 or in1 or in2 or in3 or sel or en)
      1 |-> ##0 (out === (en ? ((sel==2'b00) ? in0 :
                                 (sel==2'b01) ? in1 :
                                 (sel==2'b10) ? in2 : in3)
                              : 1'b0));
  endproperty
  assert property (p_func);

  // Internal selected must match mux choice
  property p_selected;
    @(in0 or in1 or in2 or in3 or sel)
      1 |-> ##0 (selected === ((sel==2'b00) ? in0 :
                               (sel==2'b01) ? in1 :
                               (sel==2'b10) ? in2 : in3));
  endproperty
  assert property (p_selected);

  // Disabled output forced low
  assert property (@(en or out or in0 or in1 or in2 or in3 or sel)
                   !en |-> ##0 (out === 1'b0));

  // No-X when all controls/data are known
  assert property (@(in0 or in1 or in2 or in3 or sel or en)
                   !$isunknown({en,sel,in0,in1,in2,in3}) |-> ##0 !$isunknown(out));

  // Per-select passthrough checks (redundant but localizes failures)
  assert property (@(in0 or sel or en) en && (sel==2'b00) |-> ##0 (out === in0));
  assert property (@(in1 or sel or en) en && (sel==2'b01) |-> ##0 (out === in1));
  assert property (@(in2 or sel or en) en && (sel==2'b10) |-> ##0 (out === in2));
  assert property (@(in3 or sel or en) en && (sel==2'b11) |-> ##0 (out === in3));

  // Coverage: exercise all selects (will show 2'b10/11 unreachable with 1-bit sel) and disable
  cover property (@(sel or en) en && sel==2'b00);
  cover property (@(sel or en) en && sel==2'b01);
  cover property (@(sel or en) en && sel==2'b10);
  cover property (@(sel or en) en && sel==2'b11);
  cover property (@(en) !en);

endmodule

bind MUX_4to1 MUX_4to1_sva u_mux_4to1_sva (
  .in0(in0), .in1(in1), .in2(in2), .in3(in3),
  .sel(sel), .en(en), .out(out), .selected(selected)
);