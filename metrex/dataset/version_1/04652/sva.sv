// SVA for mux32to16: concise, full functional checks + useful coverage
// Bind into DUT; uses internal nets via .*

module mux32to16_sva
(
  input  logic [31:0] out,
  input  logic [31:0] in1,
  input  logic [31:0] in2,
  input  logic        control,
  input  logic        control_not,
  input  logic [31:0] anded_out_1,
  input  logic [31:0] anded_out_2
);

  // Control complement correctness
  assert property (@(control or control_not)
                   control_not === ~control)
    else $error("control_not != ~control");

  // Internal AND legs
  assert property (@(in1 or control or anded_out_1)
                   anded_out_1 === (in1 & {32{~control}}))
    else $error("anded_out_1 != (~control)&in1");

  assert property (@(in2 or control or anded_out_2)
                   anded_out_2 === (in2 & {32{control}}))
    else $error("anded_out_2 != control&in2");

  // OR combine
  assert property (@(anded_out_1 or anded_out_2 or out)
                   out === (anded_out_1 | anded_out_2))
    else $error("out != anded_out_1 | anded_out_2");

  // End-to-end mux behavior when control is known
  assert property (@(in1 or in2 or control or out)
                   (control === 1'b0) |-> (out === in1 && anded_out_1 === in1 && anded_out_2 === '0))
    else $error("MUX failure: control=0");

  assert property (@(in1 or in2 or control or out)
                   (control === 1'b1) |-> (out === in2 && anded_out_2 === in2 && anded_out_1 === '0))
    else $error("MUX failure: control=1");

  // Legs cannot both drive 1s when control known
  assert property (@(anded_out_1 or anded_out_2 or control)
                   (control inside {1'b0,1'b1}) |-> ((anded_out_1 & anded_out_2) === '0))
    else $error("Both legs active with known control");

  // No X/Z on out when select and selected input are known
  assert property (@(in1 or control or out)
                   (control === 1'b0 && !$isunknown(in1)) |-> !$isunknown(out))
    else $error("Unknown out with control=0 and known in1");

  assert property (@(in2 or control or out)
                   (control === 1'b1 && !$isunknown(in2)) |-> !$isunknown(out))
    else $error("Unknown out with control=1 and known in2");

  // Coverage
  cover property (@(control) $rose(control));
  cover property (@(control) $fell(control));
  cover property (@(in1 or control) (control===1'b0 && $changed(in1)) ##0 (out===in1));
  cover property (@(in2 or control) (control===1'b1 && $changed(in2)) ##0 (out===in2));
  cover property (@(out) $changed(out));

endmodule

bind mux32to16 mux32to16_sva (.*);