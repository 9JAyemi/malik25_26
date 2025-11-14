// SVA for io1_sub/instio
// Bind these checks into the instio instance(s)

module instio_sva (
  input logic lower_ina, lower_io, lower_out,
  input logic sec_ina,   sec_io,   sec_out
);

  // Sample on any change of relevant signals (captures 0/1/X/Z transitions)
  default clocking cb @(lower_ina or lower_io or lower_out or
                        sec_ina   or sec_io   or sec_out); endclocking

  // Functional equivalence
  assert property (lower_out === (lower_ina | lower_io))
    else $error("lower_out != lower_ina | lower_io");
  assert property (sec_out   === (sec_ina   | sec_io))
    else $error("sec_out != sec_ina | sec_io");

  // OR dominance and zero cases (4-state safe)
  assert property ( (lower_ina === 1'b1 || lower_io === 1'b1) |-> (lower_out === 1'b1) )
    else $error("lower_out not 1 when any input is 1");
  assert property ( (sec_ina   === 1'b1 || sec_io   === 1'b1) |-> (sec_out   === 1'b1) )
    else $error("sec_out not 1 when any input is 1");

  assert property ( (lower_ina === 1'b0 && lower_io === 1'b0) |-> (lower_out === 1'b0) )
    else $error("lower_out not 0 when both inputs are 0");
  assert property ( (sec_ina   === 1'b0 && sec_io   === 1'b0) |-> (sec_out   === 1'b0) )
    else $error("sec_out not 0 when both inputs are 0");

  // No spurious output changes without input changes (glitch check)
  assert property ( !$changed(lower_ina) && !$changed(lower_io) |-> $stable(lower_out) )
    else $error("lower_out changed while inputs stable");
  assert property ( !$changed(sec_ina)   && !$changed(sec_io)   |-> $stable(sec_out) )
    else $error("sec_out changed while inputs stable");

  // Channel independence (lower activity must not disturb sec_out, and vice versa)
  assert property ( ($changed(lower_ina) || $changed(lower_io)) &&
                    !$changed(sec_ina) && !$changed(sec_io) |-> $stable(sec_out) )
    else $error("sec_out changed due to lower_* activity");
  assert property ( ($changed(sec_ina) || $changed(sec_io)) &&
                    !$changed(lower_ina) && !$changed(lower_io) |-> $stable(lower_out) )
    else $error("lower_out changed due to sec_* activity");

  // Coverage: exercise all 2-input OR truth-table outcomes (exclude X/Z by case equality)
  cover property (lower_ina === 1'b0 && lower_io === 1'b0 && lower_out === 1'b0);
  cover property (lower_ina === 1'b0 && lower_io === 1'b1 && lower_out === 1'b1);
  cover property (lower_ina === 1'b1 && lower_io === 1'b0 && lower_out === 1'b1);
  cover property (lower_ina === 1'b1 && lower_io === 1'b1 && lower_out === 1'b1);

  cover property (sec_ina   === 1'b0 && sec_io   === 1'b0 && sec_out   === 1'b0);
  cover property (sec_ina   === 1'b0 && sec_io   === 1'b1 && sec_out   === 1'b1);
  cover property (sec_ina   === 1'b1 && sec_io   === 1'b0 && sec_out   === 1'b1);
  cover property (sec_ina   === 1'b1 && sec_io   === 1'b1 && sec_out   === 1'b1);

  // Coverage: exercise Z/X cases on inouts
  cover property (lower_io === 1'bz);
  cover property (sec_io   === 1'bz);
  cover property ($isunknown(lower_out));
  cover property ($isunknown(sec_out));

endmodule

bind instio instio_sva instio_sva_i (
  .lower_ina(lower_ina), .lower_io(lower_io), .lower_out(lower_out),
  .sec_ina  (sec_ina),   .sec_io  (sec_io),   .sec_out  (sec_out)
);