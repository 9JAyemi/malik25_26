// SVA for mux81c — concise, high-quality checks and coverage
module mux81c_sva (input logic [7:0] I,
                   input logic [2:0] S,
                   input logic       Y);

  // Event-based sampling for pure combinational DUT
  default clocking cb @(I or S or Y); endclocking

  // Select must be fully known (prevents latch-like behavior on X/Z select)
  a_sel_known: assert property (!$isunknown(S));

  // Functional correctness (including X-propagation) with zero-delay settle
  a_func: assert property ( !$isunknown(S) |-> ##0 (Y === I[S]) );

  // Zero-delay response when select changes
  a_resp_sel: assert property ( $changed(S) && !$isunknown(S) |-> ##0 (Y === I[S]) );

  // Zero-delay response when selected data bit changes
  a_resp_data: assert property ( !$changed(S) && !$isunknown(S) && $changed(I[S]) |-> ##0 (Y === I[S]) );

  // Irrelevant data bit changes do not affect Y
  a_irrel_data_noeffect: assert property (
    !$changed(S) && !$isunknown(S) && $changed(I) && !$changed(I[S]) |-> ##0 !$changed(Y)
  );

  // Y only changes when driven by select or selected data changes
  a_y_changes_only_when_needed: assert property (
    $changed(Y) |-> (!$isunknown(S) && ($changed(S) || $changed(I[S])))
  );

  // Functional coverage: hit every select value and observe correct output;
  // also observe output response to selected data toggles.
  genvar k;
  for (k = 0; k < 8; k++) begin : g
    localparam logic [2:0] KV = k[2:0];
    c_sel_val:   cover property ( S == KV ##0 (Y === I[k]) );
    c_sel_dchg:  cover property ( (S == KV && $changed(I[k])) ##0 (Y === I[k]) );
  end

endmodule

// Bind into DUT
bind mux81c mux81c_sva u_mux81c_sva(.I(I), .S(S), .Y(Y));