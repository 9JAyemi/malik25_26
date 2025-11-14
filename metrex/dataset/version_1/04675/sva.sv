// SVA checker for signal_converter
// Bind this module to the DUT and connect any convenient sampling clock.
module signal_converter_sva (
  input  logic              clk,
  input  logic [3:0]        input_signal,
  input  logic [1:0]        output_signal
);

  default clocking cb @(posedge clk); endclocking

  // Combinational golden model + immediate checks (no clock dependency)
  logic [1:0] expected;
  always_comb begin
    expected = (input_signal < 6) ? (input_signal >> 1)[1:0]
                                  : (input_signal - 4)[1:0];
    assert (!$isunknown({input_signal, output_signal}))
      else $error("X/Z detected on inputs/outputs");
    assert (output_signal === expected)
      else $error("Mismatch: in=%0d out=%0d exp=%0d",
                  input_signal, output_signal, expected);
  end

  // Clocked functional check (samples every cycle)
  assert property ( output_signal
                    == ((input_signal < 6)
                        ? (input_signal >> 1)[1:0]
                        : (input_signal - 4)[1:0]) );

  // Stability: if input holds across a cycle, output must also hold
  assert property ( $stable(input_signal) |-> $stable(output_signal) );

  // Branch coverage (both sides of the conditional)
  cover property ( input_signal < 6 );
  cover property ( input_signal >= 6 );

  // Boundary value coverage with expected outputs
  cover property ( input_signal == 4'd5 && output_signal == 2'd2 );
  cover property ( input_signal == 4'd6 && output_signal == 2'd2 );

  // Full input space coverage with correctness
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : C_IN_ALL
      localparam int EXP = (i < 6) ? (i >> 1) : (i - 4);
      cover property ( input_signal == i[3:0]
                       && output_signal == EXP[1:0] );
    end
  endgenerate

  // Output value coverage (all 2-bit values observed)
  genvar o;
  generate
    for (o = 0; o < 4; o++) begin : C_OUT_ALL
      cover property ( output_signal == o[1:0] );
    end
  endgenerate

endmodule

// Example bind (provide a suitable clock from TB)
// bind signal_converter signal_converter_sva u_sva(.clk(tb_clk), .input_signal(input_signal), .output_signal(output_signal));