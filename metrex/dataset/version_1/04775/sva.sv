// SVA checker for ones_complement
module ones_complement_sva (
  input  logic [3:0] in,
  input  logic [3:0] out
);

  // Functional equivalence must always hold after any input or output change
  // Use ##0 to sample after DUT updates (avoids preponed-region race)
  assert property (@(posedge in[0] or negedge in[0]
                   or posedge in[1] or negedge in[1]
                   or posedge in[2] or negedge in[2]
                   or posedge in[3] or negedge in[3])
                   ##0 (out === ~in))
    else $error("ones_complement: out != ~in after input change");

  assert property (@(posedge out[0] or negedge out[0]
                   or posedge out[1] or negedge out[1]
                   or posedge out[2] or negedge out[2]
                   or posedge out[3] or negedge out[3])
                   ##0 (out === ~in))
    else $error("ones_complement: out changed but != ~in");

  // If input is fully known, output must be fully known
  assert property (@(posedge in[0] or negedge in[0]
                   or posedge in[1] or negedge in[1]
                   or posedge in[2] or negedge in[2]
                   or posedge in[3] or negedge in[3])
                   (!$isunknown(in)) |-> ##0 (!$isunknown(out)))
    else $error("ones_complement: known input produced unknown output");

  // Single-bit flip on input should cause single-bit flip on output (and still match ~in)
  assert property (@(posedge in[0] or negedge in[0]
                   or posedge in[1] or negedge in[1]
                   or posedge in[2] or negedge in[2]
                   or posedge in[3] or negedge in[3])
                   ($changed(in) && $countones(in ^ $past(in)) == 1)
                   |-> ##0 (out === ~in && $countones(out ^ $past(out)) == 1))
    else $error("ones_complement: single-bit flip did not propagate as expected");

  // Coverage: hit all 16 input values (and matching output)
  genvar v;
  generate
    for (v = 0; v < 16; v++) begin : C_ALL_INPUTS
      localparam logic [3:0] VAL = v[3:0];
      cover property (@(posedge in[0] or negedge in[0]
                      or posedge in[1] or negedge in[1]
                      or posedge in[2] or negedge in[2]
                      or posedge in[3] or negedge in[3])
                      ##0 (in == VAL && out === ~VAL));
    end
  endgenerate

  // Coverage: observe rises/falls on each input bit
  genvar i;
  generate
    for (i = 0; i < 4; i++) begin : C_TOGGLES
      cover property (@(posedge in[i]) ##0 (out === ~in));
      cover property (@(negedge in[i]) ##0 (out === ~in));
    end
  endgenerate

endmodule

// Bind into the DUT
bind ones_complement ones_complement_sva u_ones_complement_sva (.in(in), .out(out));