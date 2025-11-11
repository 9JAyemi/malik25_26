// SVA for parity_check
// Binds to DUT and checks parity behavior and corner cases concisely.

module parity_check_sva (
  input logic [7:0] data_in,
  input logic       control,
  input logic       parity
);

  // Functional correctness
  assert property (@(data_in or control)
    disable iff ($isunknown({control, data_in}))
    (control == 0) |-> (parity == 0)
  );

  assert property (@(data_in or control)
    disable iff ($isunknown({control, data_in}))
    (control == 1) |-> (parity == ^data_in)
  );

  // No X/Z on parity when inputs are known
  assert property (@(data_in or control)
    (!$isunknown({control, data_in})) |-> !$isunknown(parity)
  );

  // Control edge behavior
  assert property (@(data_in or control)
    disable iff ($isunknown({control, data_in}))
    $rose(control) |-> (parity == ^data_in)
  );

  assert property (@(data_in or control)
    disable iff ($isunknown({control, data_in}))
    $fell(control) |-> (parity == 0)
  );

  // Delta consistency: parity toggle equals XOR of toggled data bits when control stays 1
  assert property (@(data_in or control)
    disable iff ($isunknown({control, data_in, parity}) || $isunknown($past({control, data_in, parity})))
    (control && $past(control)) |-> ((parity ^ $past(parity)) == ^(data_in ^ $past(data_in)))
  );

  // Coverage
  cover property (@(data_in or control) $rose(control));
  cover property (@(data_in or control) $fell(control));
  cover property (@(data_in or control) (control && (^data_in == 1)));
  cover property (@(data_in or control) (control && (^data_in == 0)));
  cover property (@(data_in or control)
    (control && $past(control) && $onehot(data_in ^ $past(data_in)))
  );

endmodule

// Bind into the DUT
bind parity_check parity_check_sva sva_inst(.data_in(data_in), .control(control), .parity(parity));