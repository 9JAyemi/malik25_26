// SVA checker for o_mux
// Binds into the DUT and uses immediate assertions for combinational correctness.
// Guards against X/Z on inputs to avoid false failures.

module o_mux_sva (
  input logic O,
  input logic in0,
  input logic in1,
  input logic cbit,
  input logic prog,
  input logic sel
);

  // Combinational correctness and internal logic equivalence
  always_comb begin
    // sel must implement XOR truth table
    if (!$isunknown({prog, cbit})) begin
      assert (sel === (prog ^ cbit))
        else $error("o_mux: sel != (prog ^ cbit)");
    end

    // Output must match selected input
    if (!$isunknown({prog, cbit, in0, in1, sel})) begin
      assert (O === (sel ? in0 : in1))
        else $error("o_mux: O != (sel ? in0 : in1)");
    end
  end

  // Lightweight temporal sanity: when legs differ, O must change if sel changes
  always_comb begin
    if (!$isunknown({in0, in1, sel, O}) && (in0 !== in1) && $changed(sel)) begin
      assert ($changed(O)) else $error("o_mux: sel changed but O did not (in0!=in1)");
    end
  end

  // Coverage: exercise both select values and all prog/cbit combinations
  always_comb begin
    cover (!sel && O === in1);
    cover ( sel && O === in0);

    cover (prog==0 && cbit==0);
    cover (prog==0 && cbit==1);
    cover (prog==1 && cbit==0);
    cover (prog==1 && cbit==1);

    // Exercise both legs when inputs differ
    cover (sel && (in0 !== in1) && (O === in0));
    cover (!sel && (in0 !== in1) && (O === in1));
  end

endmodule

// Bind into the DUT; connects to internal sel
bind o_mux o_mux_sva u_o_mux_sva (.O(O), .in0(in0), .in1(in1), .cbit(cbit), .prog(prog), .sel(sel));